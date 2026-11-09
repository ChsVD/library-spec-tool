"""Per-function extraction -> spec worker; no whole-group discovery barrier."""
import copy
import hashlib
import json
import shutil
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
from pathlib import Path
from stage1.runner import snapshot
from stage1.contracts import check_evidence
from stage1.task import Budgets,ReportPolicy,run_task,write_json,write_text
from . import contracts
from .graph import new_graph,merge_discovery,install_spec,context,digest,layers
from .inventory import expand_selection,progress
from .pipeline import material_pages,render,render_graph
from .prompts import prompt
from .source_bundle import extraction_prompt,validate_extraction,materialize,merge_extraction
from .bundle_reader import verify_bundle,reader_factory,bundles_from_nodes
from .context_cards import source_index,source_cards,compact_context,writer_context
from .required_inputs import plan as required_plan
from .review_flow import run_review
from .conditional import inspect as inspect_conditions


BUNDLE_RULES = """
Reader只允许源码包中的原始区间；主模块和程序交付材料为必读，其余参考按需。writer-schema共享路径、条件和宏展开定义；edges页只交付一次，每个边ID仍须有自己的调用要求。macro_use关联共享展开定义，root/parent保留各使用场景；宏内位置不是正文直接调用。不能把省略的条件视为无条件。
仅缺已解析被调函数的行为契约时，可提出conditional_assumptions:[{id,gaps:[{source:"material_requests|spec_unknowns|extraction_unknowns",index:0}],symbol,condition,affected_claim_ids:["条款ID"],explanation}]。index为对应列表零起始索引；提取未知索引见dependency-gap-index，描述沿用gaps页中同序未知项。未知项必须原本带category:"dependency_contract",symbol才可采用；材料请求也须带category:"dependency_contract"并由symbol对应。condition须逐字出现在sections.environment，受影响条款不能标source_fact。保留原缺口；假设不是已证实保证。源码/宏/类型/声明缺失、调用覆盖未知不能用假设豁免。默认不分类仍阻断。
缺材料返回material_requests:[{symbol,question,reason}]并保留阻断未知。声明只提供接口，调用需求不是已有保证；保留字宽、容量、别名和失败状态的限制。完整宏及外围条件按原文理解，不擅自选择构建分支。只分析当前函数与记录的依赖，不搜索外部调用者。候选与包均未编译或证明。
"""


def requests(report):
    value=report.get('material_requests',[])
    if not isinstance(value,list) or any(not isinstance(v,dict) or any(not isinstance(v.get(k),str) or not v[k].strip() for k in ('symbol','question','reason')) for v in value):
        return ['material_requests needs symbol/question/reason objects']
    return []


def expansion_evidence(graph,ident,reader):
    ranges=[e['macro_expansion']['callsite'] for e in graph['edges'].values()
            if e['caller']==ident and e.get('macro_expansion')]
    return check_evidence(ranges,reader) if ranges else []


def required_details(graph,ident,reads,review=False):
    view,_=compact_context(graph,ident,max_chars=10**9)
    needed={e['detail'] for e in view['edges'] if review or e['caller']==ident}
    needed.update(u['detail'] for u in view['unknowns'])
    return ['read required dependency/unknown detail page: '+key for key in sorted(needed-set(reads))]


def spec_validator(report,reader,reads,*,node,graph,extraction=None):
    errors=contracts.specification(report,reader,reads,node=node,graph=graph)
    if isinstance(report,dict):
        errors+=requests(report)
        errors+=inspect_conditions(report,extraction or {},graph,node['id'])[0]
    errors+=expansion_evidence(graph,node['id'],reader)
    if 'writer-schema' in reads:
        _,cards=writer_context(graph,node['id'])
        errors+=['read required dependency/unknown detail page: '+key for key in cards if key not in reads]
    else:errors+=required_details(graph,node['id'],reads)
    return errors


def review_validator(report,reader,reads,*,node,spec,graph,extraction):
    errors=contracts.review(report,reader,reads,node=node,spec=spec,graph=graph)
    errors+=required_details(graph,node['id'],reads,review=True)
    errors+=expansion_evidence(graph,node['id'],reader)
    if not isinstance(report,dict):return errors
    errors+=requests(report)
    if not isinstance(report.get('checks',{}).get('bundle_completeness'),str) or not report['checks']['bundle_completeness'].strip():
        errors.append('checks.bundle_completeness required')
    if report.get('verdict')=='pass':
        if report.get('material_requests') or spec.get('material_requests'):errors.append('material gaps cannot pass')
        if any(v!='checked' for v in extraction['coverage'].values()):errors.append('incomplete extraction coverage cannot pass')
        if any(u['blocking'] for u in extraction['unknowns']):errors.append('blocking extraction gap cannot pass by conditional-scope override')
    return errors


def discovery_from_report(node,report,selected):
    """IDs and edges constructed by code; models only name local calls and sources."""
    neighbors={};edges=[]
    all_calls=report['calls']+report.get('macro_expansions',[])
    for index,call in enumerate(all_calls):
        target=call.get('target_id');decl=call.get('declaration_index')
        if target is None and decl is not None:
            snippet=report['snippets'][decl]
            target='dep-'+hashlib.sha256(json.dumps([call['symbol'],snippet['source']],sort_keys=True).encode()).hexdigest()[:20]
            neighbors[target]={'id':target,'symbol':call['symbol'],'source':snippet['source'],'configuration':'Declaration or macro identity only; conditional applicability is recorded on each call edge.'}
        if call.get('unresolved'):target=None
        root_call=report['calls'][call['root_call_index']] if index>=len(report['calls']) else call
        edges.append({'id':node['id']+'-call-'+str(index),'caller':node['id'],'callee':target,
                      'callsite':root_call['callsite'],'condition':call['condition'],
                      **({'macro_expansion':copy.deepcopy(call)} if index>=len(report['calls']) else {}),
                      'certainty':'unresolved' if target is None else 'conditional',
                      'unresolved_target':call.get('unresolved') or (call['symbol'] if target is None else '')})
    return {'function_id':node['id'],'neighbors':list(neighbors.values()),'edges':edges,
            'coverage':{'outgoing':'unknown' if any(e['callee'] is None for e in edges) else 'checked_scope',
                        'incoming':'Only selected-group direct edges are merged later; external callers not searched.'},
            'unknowns':report['unknowns']}


def replace_discovery(graph, report):
    """Replace one caller's evidence atomically, preserving other callers' edges."""
    ident=report['function_id']
    if any(e['caller']!=ident for e in report['edges']):
        raise ValueError('discovery contains another caller')
    candidate=copy.deepcopy(graph)
    old=[e for e in candidate['edges'].values() if e['caller']==ident]
    for e in old:del candidate['edges'][e['id']]
    candidate['discoveries'].pop(ident,None)
    merge_discovery(candidate,report)
    if graph['discoveries'].get(ident)!=report:
        affected={e['callee'] for e in old+report['edges'] if e['callee']}
        affected.add(ident)
        for key in affected:
            n=candidate['nodes'][key]
            if n['status']=='reviewed_candidate':n['status']='needs_recheck'
    graph.clear();graph.update(candidate)




def run_pipeline(root,output,manifest,materials,factory,*,prepared_source=None,**kwargs):
    """Current public entry: immutable reviewed sources, never automatic extraction."""
    if prepared_source is None:
        raise ValueError('independent source preparation and review required before specification')
    return run_combined_pipeline(root,output,manifest,materials,factory,prepared_source=prepared_source,**kwargs)


def run_combined_pipeline(root,output,manifest,materials,factory,*,budgets=None,batch_size=2,concurrency=2,
                 max_revisions=1,resume=False,label='fixture',model_identity=None,local_chars=18000,prepared_source=None):
    import fcntl
    root=Path(root).resolve(strict=True);output=Path(output).resolve()
    if output.is_relative_to(root):raise ValueError('output must be outside input')
    if manifest.get('version')==2:manifest=expand_selection(root,manifest)
    if not manifest.get('selection_inventory'):raise ValueError('bundled workflow requires complete module/group inventory')
    if min(batch_size,concurrency,local_chars)<1 or max_revisions<0:raise ValueError('invalid limits')
    inventory=snapshot(root)
    if manifest.get('expected_input_snapshot',inventory)!=inventory:raise ValueError('input changed from stage1')
    prepared=None
    if prepared_source is not None:
        if output.is_relative_to(Path(prepared_source).resolve()):raise ValueError('spec output must be outside reviewed preparation')
        from .prepare import load_approved
        prepared=load_approved(prepared_source,manifest,inventory)
        manifest=copy.deepcopy(manifest)
        manifest['functions']=[copy.deepcopy(prepared['functions'][n['id']]['node']) for n in manifest['functions']]
    identity={'workflow':'source-bundles-v1','context_policy':9,'prepared_digest':digest(prepared) if prepared else None,'input_root':str(root),'manifest':manifest,'materials':{k:digest(v) for k,v in materials.items()},'model':model_identity or {'mode':label},'mode':label}
    if not resume:output.mkdir(parents=True,exist_ok=False)
    elif not output.is_dir():raise ValueError('resume directory missing')
    with (output/'run.lock').open('a') as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:raise ValueError('run already active')
        if resume:
            if json.loads((output/'identity.json').read_text())!=identity:raise ValueError('workflow/input/model changed; legacy runs need a new output directory')
            if json.loads((output/'input_snapshot.json').read_text())!=inventory:raise ValueError('input changed')
            state=json.loads((output/'status.json').read_text());graph=json.loads((output/'graph.json').read_text())
            if state.get('graph_digest')!=digest(graph):raise ValueError('graph/status mismatch')
        else:
            state={'stage':2,'workflow':'source-bundles-v1','mode':label,'status':'running','attempt':0,'tasks':{},'proof_status':'not_proved'}
            graph=new_graph(manifest);write_json(output/'identity.json',identity);write_json(output/'input_snapshot.json',inventory)
        budgets=budgets or Budgets(calls=24,context_chars=60000)
        state['attempt']+=1;attempt=state['attempt'];state['status']='running'
        def persist():
            write_json(output/'graph.json',graph);write_text(output/'graph.md',render_graph(graph))
            state['graph_digest']=digest(graph);state['selection_progress']=progress(graph)
            write_json(output/'selection_progress.json',progress(graph));write_json(output/'selection_inventory.json',graph['selection_inventory'])
            write_json(output/'status.json',state)
        def load_bundle(node):
            return bundles_from_nodes(output,[node],inventory)[0]
        for n in graph['nodes'].values():
            if n.get('source_bundle'):load_bundle(n)
        persist()
        if graph['selection_inventory']['scope_status']!='enumerated':
            state['status']='needs_scope_review';persist();return state
        selected={n['id']:n for n in manifest['functions']}
        cards=[{k:n[k] for k in ('id','symbol','source','configuration')} for n in selected.values()]
        def task(role,ident,revision,assignment,artifacts,validator,bundles=None,required=None):
            tid=f'{ident}-{attempt}-{revision}-{role}'
            if role=='review':
                reviewed=run_review(root,output/'tasks'/tid,factory,node=validator.keywords['node'],
                    spec=validator.keywords['spec'],graph=validator.keywords['graph'],artifacts=artifacts,
                    bundles=bundles,budgets=budgets,label=label)
                write_json(output/'tasks'/tid/'status.json',{k:v for k,v in reviewed.items() if k!='report'})
                return reviewed
            return run_task(root,output/'tasks'/tid,factory(role,tid),
                extraction_prompt(assignment['function'],[c for c in cards if c['source']['path']==assignment['function']['source']['path']][:16])+ '\n补充任务：'+json.dumps(assignment,ensure_ascii=False) if role=='extract_source' else prompt(role,assignment)+BUNDLE_RULES+("\nSOURCE PREPARATION ALREADY REVIEWED: target and dependencies are human-reviewed adapted source, not verbatim original library. Use supplied processed callee-contracts as interfaces; do not request callee bodies or reconstruct them. Report contradictions/missing contracts back to the independent preparation step. Do not infer unavailable callee contracts. Cite prepared paths as adapted input, not original-library facts." if prepared is not None else ''),
                validator,role=role,task_id=tid,budgets=budgets,artifacts=artifacts,label=label,allow_report_patch=True,
                reader_factory=reader_factory(bundles) if bundles is not None else None,
                report_policy=ReportPolicy(append_batches=True) if role in ('write','review') else None,required_inputs=required,complete_bundle_evidence=True)
        def worker(node):
            ident=node['id'];result={'id':ident,'tasks':{},'status':'incomplete'}
            folder=output/'functions'/ident;folder.mkdir(parents=True,exist_ok=True)
            pack=None;report=None;previous=node.get('spec');review=node.get('review');missing=(review or {}).get('material_requests') or (previous or {}).get('material_requests',[])
            if node.get('source_bundle'):pack=load_bundle(node);report=pack[1]['report']
            for revision in range(max_revisions+1):
                if prepared is not None and pack is None:
                    item=prepared['functions'][ident];destination=output/'examples'/ident/'prepared'
                    destination.mkdir(parents=True,exist_ok=False)
                    m=copy.deepcopy(item['bundle'])
                    for name in m['files']:shutil.copyfile(Path(prepared_source)/name,destination/name)
                    write_json(destination/'manifest.json',m);verify_bundle(destination,m)
                    pack=(destination,m);report=copy.deepcopy(m['report'])
                    result['source_bundle']={'path':str(destination.relative_to(output)),'manifest_digest':digest(m)}
                    write_json(folder/'bundle_progress.json',{'source_bundle':result['source_bundle'],'status':'reviewed_source_imported'})
                if prepared is not None and missing:
                    result.update(status='needs_source_revision',reason='Return missing material to independent source preparation; do not reextract during specification.')
                    write_json(folder/'source_revision_request.json',{'material_requests':missing,'proof_status':'not_proved'})
                    return result
                if pack is None or missing:
                    if pack is not None:verify_bundle(*pack)
                    assignment={'function':selected[ident],'material_requests':missing,'rule':'Only this implementation, direct callee declarations and transitive type/macro prerequisites; no caller search. Retain missing behavior contracts.'}
                    artifacts=material_pages(selected[ident],materials)
                    for offset in range(0,len(cards),16):artifacts['selected-identities:'+str(offset//16+1)]=cards[offset:offset+16]
                    if report:artifacts['previous_extraction']=report
                    r=task('extract_source',ident,revision,assignment,artifacts,partial(validate_extraction,node=selected[ident],selected=selected))
                    result['tasks']['extract-'+str(revision)]={k:r.get(k) for k in ('status','calls','reason')}
                    if r['status']!='task_completed':
                        result.update(status='needs_material' if r['status']=='needs_material' else 'incomplete',reason=r.get('reason'))
                        return result
                    report=merge_extraction(report,r['report']);destination=output/'examples'/ident/f'v{attempt}-{revision}'
                    destination.parent.mkdir(parents=True,exist_ok=True)
                    m=materialize(root,destination,selected[ident],report);pack=(destination,m)
                    versions={x['path']:x.get('sha256') for x in inventory}
                    if any(versions.get(x['original']['path'])!=x['sha256'] for x in m['mappings']):raise ValueError('source changed while extracting')
                    result['source_bundle']={'path':str(destination.relative_to(output)),'manifest_digest':digest(m)}
                    write_json(folder/'bundle_progress.json',{'source_bundle':result['source_bundle'],'status':'extracted_not_reviewed'})
                elif 'source_bundle' not in result:result['source_bundle']=node['source_bundle']
                disc=discovery_from_report(selected[ident],report,selected)
                result['discovery']=disc
                local=new_graph(manifest);merge_discovery(local,disc)
                view,detail_cards=writer_context(local,ident,local_chars);view['scope']='Own source bundle and direct calls only; external caller search deferred.'
                artifacts=material_pages(selected[ident],materials);artifacts.update(source_cards([pack]));artifacts.update(detail_cards)
                if report.get('callee_contracts'):artifacts['callee-contracts']=report['callee_contracts']
                artifacts['dependency-gap-index']={'extraction_unknowns':[{'index':i,**{k:u[k] for k in ('category','symbol') if k in u}} for i,u in enumerate(report['unknowns'])]}
                if previous:artifacts['previous_candidate']=previous
                if review:artifacts['revision_review']=review
                r=task('write',ident,revision,view,artifacts,partial(spec_validator,node=selected[ident],graph=local,extraction=report),[pack],
                       required_plan(selected[ident],local,artifacts,bundles=[pack]))
                result['tasks']['write-'+str(revision)]={k:r.get(k) for k in ('status','calls','reason')}
                if r['status']!='task_completed':
                    result.update(status='needs_material' if r['status']=='needs_material' else 'incomplete',reason=r.get('reason'))
                    if prepared is not None:write_json(folder/'source_revision_request.json',{'reason':r.get('reason'),'task_status':r['status'],'instruction':'Inspect task diagnostics; source changes require independent preparation and review.'})
                    return result
                previous=r['report'];result['spec']=previous
                write_json(folder/f'candidate-{attempt}-{revision}.json',previous);write_text(folder/f'candidate-{attempt}-{revision}.md',render(previous))
                write_json(folder/'candidate.json',previous);write_text(folder/'candidate.md',render(previous))
                r=task('review',ident,revision,view,{**artifacts,'candidate':previous},partial(review_validator,node=selected[ident],spec=previous,graph=local,extraction=report),[pack],
                       required_plan(selected[ident],local,{**artifacts,'candidate':previous},review=True,candidate=previous))
                result['tasks']['review-'+str(revision)]={k:r.get(k) for k in ('status','calls','reason')}
                if r['status']!='task_completed':
                    result.update(status='needs_material' if r['status']=='needs_material' else 'incomplete',reason=r.get('reason'))
                    return result
                review=r['report'];result['review']=review;result['status']='local_reviewed' if review['verdict']=='pass' else review['verdict']
                write_json(folder/f'review-{attempt}-{revision}.json',review)
                missing=review.get('material_requests') or previous.get('material_requests',[])
                if prepared is not None and missing:
                    result.update(status='needs_source_revision')
                    write_json(folder/'source_revision_request.json',{'material_requests':missing,'proof_status':'not_proved'})
                    break
                if review['verdict']=='pass' or (review['verdict']!='needs_revision' and not missing):break
            return result
        try:
            ids=[n['id'] for n in manifest['functions'] if graph['nodes'][n['id']]['status']!='reviewed_candidate']
            for start in range(0,len(ids),batch_size):
                batch=ids[start:start+batch_size]
                with ThreadPoolExecutor(max_workers=min(concurrency,batch_size)) as pool:
                    jobs={pool.submit(worker,copy.deepcopy(graph['nodes'][i])):i for i in batch}
                    for future in as_completed(jobs):
                        ident=jobs[future]
                        try:r=future.result()
                        except Exception as exc:
                            r={'id':ident,'status':'incomplete','reason':str(exc),'tasks':{}}
                            saved=output/'functions'/ident/'bundle_progress.json'
                            if saved.exists():
                                r['source_bundle']=json.loads(saved.read_text())['source_bundle']
                        state['tasks'][ident]=r.get('tasks',{})
                        if r.get('discovery'):
                            try:replace_discovery(graph,r['discovery'])
                            except ValueError as exc:
                                graph['nodes'][ident].update(status='incomplete',failure_reason=str(exc))
                                persist()
                                continue
                        node=graph['nodes'][ident]
                        if r.get('source_bundle'):node['source_bundle']=r['source_bundle']
                        if r.get('spec') and r.get('review'):install_spec(graph,ident,r['spec'],r['review'])
                        elif r.get('spec'):node['spec']=r['spec'];node['revision']+=1
                        node=graph['nodes'][ident];node['status']=r['status']
                        if r.get('reason'):node['failure_reason']=r['reason']
                        persist()
                if snapshot(root)!=inventory:raise ValueError('input changed during extraction')
            write_json(output/'schedule.json',layers(graph))
            # Full selected-group incident edges now exist. Review one function and
            # only its adjacent source bundles; no global raw-source Reader.
            frozen=copy.deepcopy(graph)
            for ident,node in graph['nodes'].items():
                if not node['selected'] or node['status'] not in ('local_reviewed','needs_recheck'):continue
                adjacent={x for e in graph['edges'].values() if ident in (e['caller'],e['callee']) for x in (e['caller'],e['callee']) if x and x!=ident}
                packs=[load_bundle(node)]+[load_bundle(graph['nodes'][i]) for i in sorted(adjacent) if graph['nodes'][i].get('source_bundle')]
                artifacts=material_pages(selected[ident],materials);artifacts['candidate']=node['spec'];artifacts.update(source_cards(packs))
                group_view,detail_cards=compact_context(frozen,ident,local_chars);artifacts.update(detail_cards)
                for i in adjacent:
                    if frozen['nodes'][i]['spec']:artifacts['neighbor:'+i]=frozen['nodes'][i]['spec']
                r=task('review',ident,'group',group_view,artifacts,
                       partial(review_validator,node=selected[ident],spec=node['spec'],graph=frozen,extraction=packs[0][1]['report']),packs,
                       required_plan(selected[ident],frozen,artifacts,review=True,candidate=node['spec']))
                state['tasks'].setdefault(ident,{})['group-review']={k:r.get(k) for k in ('status','calls','reason')}
                if r['status']=='task_completed':
                    node['review']=r['report'];node['status']='reviewed_candidate' if r['report']['verdict']=='pass' else r['report']['verdict']
                    node['reviewed_against']={i:digest(frozen['nodes'][i]['spec']) for i in adjacent if frozen['nodes'][i]['spec']}
                    write_json(output/'functions'/ident/'group-review.json',r['report'])
                else:node['status']='needs_material' if r['status']=='needs_material' else 'incomplete'
                persist()
            if snapshot(root)!=inventory:raise ValueError('input changed')
            for node in graph['nodes'].values():
                if node.get('source_bundle'):load_bundle(node)
            state['status']='candidates_reviewed' if progress(graph)['all_selected_complete'] else 'incomplete'
        except (Exception,KeyboardInterrupt) as exc:
            state.update(status='interrupted' if isinstance(exc,KeyboardInterrupt) else 'incomplete',reason=str(exc))
        persist()
        write_text(output/'SUMMARY.md','# 源码包与自然规约\n\n状态：'+state['status']+'\n\n'+ '\n'.join('- '+n['symbol']+'：'+n['status']+('；[规约](functions/'+i+'/candidate.md)' if n['spec'] else '') for i,n in graph['nodes'].items() if n['selected'])+'\n\n全部候选均未证明；源码包尚未经过 QCP 编译。\n')
        return state


def export_examples(run, destination):
    """Explicit export only, no replacement of an existing QCP example directory."""
    run=Path(run).resolve(strict=True);destination=Path(destination).resolve()
    if destination.exists() or destination.is_relative_to(run):raise ValueError('export requires a new directory outside the run')
    identity=json.loads((run/'identity.json').read_text())
    if identity.get('input_root') and destination.is_relative_to(Path(identity['input_root']).resolve()):raise ValueError('export must not modify input')
    graph=json.loads((run/'graph.json').read_text());status=json.loads((run/'status.json').read_text())
    if status.get('graph_digest')!=digest(graph):raise ValueError('graph/status mismatch')
    packages=[]
    for ident,node in graph['nodes'].items():
        if not node['selected'] or not node.get('source_bundle'):continue
        record=node['source_bundle'];folder=(run/record['path']).resolve(strict=True)
        if not folder.is_relative_to(run):raise ValueError('bundle escapes run')
        m=json.loads((folder/'manifest.json').read_text())
        if digest(m)!=record['manifest_digest']:raise ValueError('manifest changed')
        verify_bundle(folder,m);packages.append((ident,folder,m))
    if not packages:raise ValueError('no extracted source bundles to export')
    destination.mkdir(parents=True,exist_ok=False)
    for ident,folder,m in packages:
        target=destination/ident;target.mkdir()
        for name in m['files']:
            p=target/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(folder/name,p)
        write_json(target/'manifest.json',m)
    write_text(destination/'README.md','Extracted source excerpts only. Not QCP-compiled or proved. Review macro configuration, dependencies and contracts before use.\n')
    return len(packages)
