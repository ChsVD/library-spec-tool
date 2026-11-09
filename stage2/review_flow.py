"""Independent bounded review jobs; deterministic, fail-closed aggregation."""
import copy
import json
from functools import partial
from stage1.contracts import check_evidence
from stage1.task import run_task, ReportPolicy, write_json
from .bundle_reader import BundleReader, reader_factory
from .context_cards import source_index
from .contracts import all_evidence, CHECKS
from .graph import digest
from .conditional import inspect as inspect_conditions, review_checks, catalog


def read_actions(evidence):
    merged=[]
    for e in sorted(evidence,key=lambda x:(x['path'],x['start'],x['end'])):
        if merged and merged[-1]['path']==e['path'] and e['start']<=merged[-1]['end']+1:
            merged[-1]['end']=max(merged[-1]['end'],e['end'])
        else: merged.append(dict(e))
    return [{'tool':'read','path':e['path'],'start':i,'count':min(80,e['end']-i+1)}
            for e in merged for i in range(e['start'],e['end']+1,80)]


def jobs(node,spec,graph,artifacts,bundles):
    """Quality sees requirements; consistency jobs see complete code and scoped obligations."""
    primary='material:'+node['materials'][0]+':' if node.get('materials') else None
    quality={'candidate':spec,'source-index':source_index(bundles),**{k:v for k,v in artifacts.items() if primary and k.startswith(primary)}}
    base={'function':{k:node[k] for k in ('id','symbol','source','configuration')},'edges':[]}
    caller_needs=[]
    for edge in graph['edges'].values():
        if edge['callee']==node['id'] and graph['nodes'][edge['caller']].get('spec'):
            caller_needs.extend(x for x in graph['nodes'][edge['caller']]['spec']['call_requirements'] if x['edge_id']==edge['id'])
    if caller_needs:quality['caller-needs']=caller_needs
    interfaces=[c for _,m in bundles for c in m['report'].get('callee_contracts',[])]
    interface_evidence=[c['source'] for c in interfaces]
    if interfaces:quality['callee-contracts']=interfaces
    reference_evidence=[e for x in spec['reference_uses'] for e in x['evidence']]+interface_evidence
    result=[('quality',base,quality,reference_evidence,('strength','preconditions','boundaries','representation','evidence'))]
    incident=[e for e in graph['edges'].values() if node['id'] in (e['caller'],e['callee'])]
    # One behavior check, then small groups of call obligations. Never truncate edges.
    for number,edges in enumerate([[]]+[incident[i:i+4] for i in range(0,len(incident),4)]):
        ids={e['id'] for e in edges}
        candidate={k:copy.deepcopy(spec[k]) for k in ('function_id','proof_status','sections','unknowns')}
        candidate['conditional_assumptions']=copy.deepcopy(spec.get('conditional_assumptions',[]))
        conditional_claims={i for a in spec.get('conditional_assumptions',[]) for i in a['affected_claim_ids']}
        candidate.update(claims=spec['claims'] if number==0 else [c for c in spec['claims'] if c['id'] in conditional_claims],reference_uses=spec['reference_uses'] if number==0 else [],
                         call_requirements=[x for x in spec['call_requirements'] if x['edge_id'] in ids],
                         caller_scenarios=[x for x in spec['caller_scenarios'] if x['edge_id'] in ids])
        supplied={'candidate':candidate,'source-index':source_index(bundles)}
        if interfaces:supplied['callee-contracts']=interfaces
        evidence=[node['source']]+all_evidence(candidate)+interface_evidence
        for e in edges:
            evidence.append(e['callsite'])
            if e.get('macro_expansion'):evidence.append(e['macro_expansion']['callsite'])
            other=e['callee'] if e['caller']==node['id'] else e['caller']
            if other and graph['nodes'][other].get('spec'):
                neighbor=graph['nodes'][other]['spec']
                supplied['neighbor:'+other]={k:neighbor[k] for k in ('function_id','proof_status','sections')}
                supplied['neighbor:'+other]['conditional_assumptions']=copy.deepcopy(neighbor.get('conditional_assumptions',[]))
                supplied['neighbor:'+other]['call_requirements']=[x for x in neighbor['call_requirements'] if x['edge_id'] in ids]
        for _,m in bundles:
            for unit in m.get('macro_units',[]):
                source=unit['source']
                if any(e['path']==source['path'] and e['start']<=source['end'] and source['start']<=e['end'] for e in evidence):
                    evidence.append(source)
                    evidence.extend(c['source'] for c in unit['conditions'])
            for snippet in m['report']['snippets']:
                source=snippet['source']
                if snippet['kind']=='macro' and any(e['path']==source['path'] and e['start']<=source['end'] and source['start']<=e['end'] for e in evidence):
                    evidence.append(source)
        result.append(('behavior' if number==0 else 'calls-'+str(number),{**base,'edges':edges},supplied,evidence,('call_requirements','boundaries','representation','evidence')))
    return result


def validate(report,reader,reads,*,ident,keys,required_artifacts,evidence,assumptions=()):
    errors=[]
    if not isinstance(report,dict):return ['review report must be an object']
    errors+=review_checks(report,assumptions)
    if report.get('function_id')!=ident:errors.append('wrong function identity')
    if report.get('verdict') not in ('pass','needs_revision','insufficient'):errors.append('invalid scoped review verdict')
    for key in keys:
        if not isinstance(report.get('checks',{}).get(key),str) or not report['checks'][key].strip():errors.append('missing check: '+key)
    for key in required_artifacts:
        if key not in reads:errors.append('review must inspect '+key)
    errors+=check_evidence(evidence,reader,required=False)
    errors+=check_evidence(report.get('evidence',[]),reader,required=False)
    material=report.get('material_requests',[])
    if not isinstance(material,list) or any(not isinstance(x,dict) or any(not isinstance(x.get(k),str) or not x[k].strip() for k in ('symbol','question','reason')) for x in material):
        errors.append('invalid material_requests')
    findings=report.get('findings')
    if not isinstance(findings,list):return errors+['findings must be a list']
    for finding in findings:
        if not isinstance(finding,dict) or not isinstance(finding.get('description'),str) or not finding['description'].strip() or type(finding.get('blocking')) is not bool:
            errors.append('finding requires description and blocking');continue
        if finding['blocking'] and report.get('verdict')=='pass':errors.append('blocking finding cannot pass')
        if 'call_requirements' in keys and finding['blocking'] and report.get('verdict')=='needs_revision':
            if not all(isinstance(finding.get(k),str) and finding[k].strip() for k in ('input','actual','required')):
                errors.append('behavior mismatch requires concrete input, actual behavior and required behavior; use insufficient if unknown')
    if report.get('material_requests') and report.get('verdict')=='pass':errors.append('material requests cannot pass')
    return errors


def run_review(root,folder,factory,*,node,spec,graph,artifacts,bundles,budgets,label):
    folder.mkdir(parents=True,exist_ok=True)
    ident=node['id']; extraction=bundles[0][1]['report']
    fingerprint=digest({'spec':spec,'edges':graph['edges'],'bundles':[m for _,m in bundles]})
    condition_errors,covered=inspect_conditions(spec,extraction,graph,ident)
    assumptions=spec.get('conditional_assumptions',[])
    requests=[r for i,r in enumerate(spec.get('material_requests',[])) if ('material_requests',i) not in covered]
    blockers=condition_errors+[u['description'] for source,items in [('spec_unknowns',spec['unknowns']),('extraction_unknowns',extraction['unknowns'])] for i,u in enumerate(items) if u.get('blocking') and (source,i) not in covered]
    if any(v!='checked' for v in extraction['coverage'].values()):blockers.append('extraction coverage incomplete')
    if graph['discoveries'].get(ident,{}).get('coverage',{}).get('outgoing')=='unknown':blockers.append('outgoing coverage unresolved')
    if any(e['caller']==ident and (e.get('callee') is None or e.get('certainty')=='unresolved') for e in graph['edges'].values()):blockers.append('unresolved outgoing call target')
    planned=jobs(node,spec,graph,artifacts,bundles) if not condition_errors else []
    reader=BundleReader(root,folder/'preflight-reads.jsonl',bundles=bundles)
    # This audit gives no credit to any model. Each job receives its own inputs below.
    gaps=[]
    for action in read_actions([e for _,_,_,evidence,_ in planned for e in evidence]):
        response=reader.execute(action)
        if response.get('error') or response.get('end',0)<action['start']+action['count']-1:gaps.append(action)
    preflight={'fingerprint':fingerprint,'material_requests':requests,'blockers':blockers,'missing_source_actions':gaps,
               'conditional_assumptions':assumptions,'conditional_gap_refs':[{'source':s,'index':i} for s,i in sorted(covered)],
               'jobs':[name for name,*_ in planned],'proof_status':'not_proved'}
    if node.get('materials') and not any(k.startswith('material:'+node['materials'][0]+':') for k in artifacts):
        blockers.append('required primary module missing')
    write_json(folder/'preflight.json',preflight)
    if requests or blockers or gaps:
        report={'function_id':ident,'verdict':'needs_revision' if requests else 'insufficient',
                'checks':{'bundle_completeness':'Program preflight found unresolved material or coverage; no semantic review performed.'},
                'findings':[{'description':x,'blocking':True} for x in blockers],
                'material_requests':requests,'evidence':[],'tool_evidence':[],'preflight':preflight}
        write_json(folder/'report.json',report)
        return {'status':'task_completed','reason':'preflight_requires_material','calls':0,'report':report}
    outcomes=[];calls=0
    for name,assignment,supplied,evidence,keys in planned:
        quality=name=='quality'
        if assumptions:
            all_gaps=catalog(spec,extraction)
            supplied['conditional-gaps']=[{'source':s,'index':i,'gap':all_gaps[s][i]} for s,i in sorted(covered)]
        instruction=('检查规约是否覆盖模块职责及需求、前提是否过强、保证是否过弱、参考适配是否有依据。不要根据实现恰好符合规约就判定规约充分。必要时按需读源码或参考材料。'
                     if quality else '仅检查本任务所列行为或调用义务与实现是否一致。完整目标实现保留控制流；核对宏条件。对冲突给出具体输入、实际行为、要求行为。无法确定用insufficient，不编造反例。邻居规约和被调函数需求均未证明。')
        if any(m.get('source_kind')=='reviewed_preparation' for _,m in bundles):instruction+=' 当前材料是人工审核后的适配代码；callee-contracts为预先处理的接口，按其条件检查调用，不递归推断callee实现。适配代码不是原库逐字事实。'
        assignment={**assignment,'review_scope':name,'checks':list(keys)}
        if assumptions:
            assignment['conditional_assumption_ids']=[a['id'] for a in assumptions]
            instruction+=' 候选conditional_assumptions尚未证实；逐项检查是否误把源码缺失当契约缺失、过强排除合法输入、循环假设目标结论、与已读实现冲突，当前职责内不确定则unknown。输出assumption_checks:[{id,decision:acceptable_condition/reject/unknown,explanation}]必须覆盖每个ID，全部acceptable_condition才允许pass；pass只表示带条件的候选适合后续，不表示依赖保证已成立。'
        prompt='独立自然语言候选审查；不是形式证明。只返回JSON动作read/artifact/finish/patch_report。'+instruction+' 输出finish.report包含function_id,verdict(pass/needs_revision/insufficient),checks(各项说明),findings([{description,blocking,input,actual,required}]),evidence([{path,start,end}]),material_requests。引用原文必须由本任务实际读取。只报告当前范围，不重写完整规约。\n任务：\n'+json.dumps(assignment,ensure_ascii=False)
        required=[{'tool':'artifact','id':key} for key in supplied]+read_actions(evidence)
        tid=folder.name+'-'+name
        state=run_task(root,folder/name,factory('review',tid),prompt,
                       partial(validate,ident=ident,keys=keys,required_artifacts=supplied,evidence=evidence,assumptions=assumptions),
                       role='review',task_id=tid,budgets=budgets,artifacts=supplied,label=label,
                       allow_report_patch=True,reader_factory=reader_factory(bundles),report_policy=ReportPolicy(max_report_chars=6000,append_batches=True),required_inputs=required,complete_bundle_evidence=True)
        calls+=state['calls']
        if state['status']!='task_completed':return {**state,'calls':calls}
        outcomes.append({'job':name,'report':state['report']})
        write_json(folder/'completed-checks.json',outcomes)
    verdict='pass' if all(x['report']['verdict']=='pass' for x in outcomes) else ('needs_revision' if any(x['report']['verdict']=='needs_revision' for x in outcomes) else 'insufficient')
    report={'function_id':ident,'verdict':verdict,'proof_status':'not_proved','fingerprint':fingerprint,
            'checks':{**{k:'; '.join(x['job']+': '+x['report']['checks'][k] for x in outcomes if k in x['report']['checks']) for k in CHECKS},
                      'bundle_completeness':'Program preflight passed; extraction claims are not compiler validation.',
                      'tool_support':'QCP support is deferred to formalization; no unsupported-tool verdict inferred.'},
            'conditional_assumptions':copy.deepcopy(assumptions),'conditional_gap_refs':preflight['conditional_gap_refs'],
            'acceptance_scope':'conditional_candidate_not_proved' if assumptions else 'candidate_not_proved',
            'findings':[f for x in outcomes for f in x['report']['findings']],
            'material_requests':[r for x in outcomes for r in x['report'].get('material_requests',[])],
            'evidence':[],'tool_evidence':[],'scoped_checks':outcomes}
    write_json(folder/'report.json',report)
    return {'status':'task_completed','reason':'scoped_reviews_aggregated','calls':calls,'report':report}
