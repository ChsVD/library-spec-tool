"""Persisted per-function extraction, common candidates and independent review."""
import json
from functools import partial
from pathlib import Path
from stage1.runner import snapshot
from stage1.task import Budgets, run_task, write_json, write_text
from stage2.graph import digest
from stage2.inventory import progress
from stage2.bundle_reader import bundles_from_nodes, reader_factory
from . import contracts, planning, materials, strategies
from .prompts import prompt


def load_upstream(root, source, input_transition=None):
    source=Path(source).resolve(strict=True)
    graph=json.loads((source/'graph.json').read_text())
    status=json.loads((source/'status.json').read_text())
    if (source/'input_changed.json').exists():
        raise ValueError('stage2 input changed during generation; results are stale')
    reference=graph.get('status')=='unverified_reference_graph'
    if reference:
        from stage3.reference import validate
        from stage3.reference_review import approved, validate_review
        identity=json.loads((source/'identity.json').read_text())
        inventory=identity['input_snapshot']
        reviewed=status.get('status')=='reviewed_reference_drafts'
        if status.get('status') not in ('drafts_generated','reviewed_reference_drafts'):
            raise ValueError('stage2 must complete all selected reference drafts')
        if status.get('semantic_review') is not reviewed or status.get('proved') is not False:
            raise ValueError('reference review/proof status mismatch')
        if status.get('review_required') and not reviewed:
            raise ValueError('required stage2 review has not completed')
        if reviewed and (not status.get('review_required') or not identity.get('review_policy')):
            raise ValueError('review policy missing')
        if status.get('graph_digest',digest(graph))!=digest(graph):
            raise ValueError('stage2 graph/status mismatch')
        expected=status.get('expected_function_ids')
        if expected is None:
            # Older reference runs did not save their final continuation scope.
            if identity.get('seed_digest'):
                raise ValueError('resume stage2 first to record its continuation scope')
            expected=[n['id'] for n in identity['manifest']['functions']]
        nodes=graph['nodes']
        if not expected or len(set(expected))!=len(expected) or set(nodes)!=set(expected):
            raise ValueError('stage2 reference scope is incomplete')
        for ident,n in nodes.items():
            if n.get('id')!=ident or n.get('selected') is not True or n.get('status')!='reference_draft':
                raise ValueError('selected function lacks reference draft')
            validate({'functions':[n.get('spec')]},[ident])
            if reviewed:
                if not approved(n):raise ValueError('review missing or stale')
                validate_review({'functions':[n['review']]},[ident])
        selection=identity['manifest'].get('selection_inventory',{}).get('selection',{})
        graph['selection_inventory']={'selection':selection,'expected_function_ids':expected,
                                      'gaps':graph.get('inventory_gaps',[])}
        graph['upstream_context']={'kind':'reviewed_reference_drafts' if reviewed else 'reference_drafts','semantic_review':reviewed,'proved':False,
            'expected_function_ids':expected,'unknown_calls':graph.get('unknown_calls',[]),
            'inventory_gaps':graph.get('inventory_gaps',[]),
            'conditions':contracts.upstream_conditions(nodes)}
        # Include status/identity changes in the stage3 resume and in-flight digest.
        if graph.get("scope_plan"):
            from stage2.demand_scope import validate_plan
            from stage3.reference import validate_scoped
            plan=validate_plan(graph["scope_plan"])
            if (identity.get("scope_plan_digest") != plan["plan_digest"]
                    or status.get("scope_plan_digest") != plan["plan_digest"]
                    or status.get("scope_approved") is not True
                    or set(plan["generation_ids"]) != set(nodes)
                    or status.get("target_function_ids") != plan["target_ids"]):
                raise ValueError("demand scope approval/coverage mismatch")
            targets=set(plan["target_ids"]); demands=set(plan["demand_ids"])
            if not targets or targets & demands or targets | demands != set(nodes):
                raise ValueError("invalid target/demand partition")
            if any(n.get("role") != ("target" if i in targets else "demand") for i,n in nodes.items()):
                raise ValueError("demand scope role mismatch")
            validate_scoped({"functions":[n["spec"] for n in nodes.values()]},list(nodes),graph)
            def background(n):
                return {k:n[k] for k in ("id","symbol","source","configuration","spec","role","context_trust") if k in n}
            graph["upstream_context"].update(
                generation_function_ids=expected, expected_function_ids=sorted(targets),
                conditions=contracts.upstream_conditions({i:nodes[i] for i in targets}),
                demand_conditions=contracts.upstream_conditions({i:nodes[i] for i in demands}),
                demand_context=[background(nodes[i]) for i in sorted(demands)],
                boundary_context=[background(n) for n in graph.get("boundary_nodes",{}).values()],
                boundary_edges=graph.get("boundary_edges",[]), scope_plan_digest=plan["plan_digest"],
                scope_note="Generate common content for target IDs only; demand/context functions are unproved background")
            if plan["version"] >= 2:
                graph["upstream_context"]["dependency_scope"] = {
                    k:plan[k] for k in ("requested_target_ids", "dependency_added_target_ids",
                        "scc_added_target_ids", "dependency_boundaries", "dependency_boundary_ids",
                        "dependency_status", "target_unknown_calls", "proof_order_components",
                        "proof_order_note")}
            nodes={i:n for i,n in nodes.items() if i in targets}
            graph["selection_inventory"]["expected_function_ids"]=sorted(targets)
            graph["selection_inventory"]["selection"]={**selection, "kind":"function_group",
                "target_function_ids":sorted(targets), "scope_plan_digest":plan["plan_digest"],
                "scope_note":"Only target functions are common-content work items; parent module paths are provenance"}
        graph['upstream_identity_digest']=digest(identity)
        graph['upstream_status_digest']=digest(status)
    else:
        if status.get('status')!='candidates_reviewed' or status.get('graph_digest')!=digest(graph):
            raise ValueError('stage2 must have a consistent reviewed checkpoint')
        if not graph.get('selection_inventory') or not progress(graph)['all_selected_complete']:
            raise ValueError('stage2 must cover the complete selected module/group')
        inventory=json.loads((source/'input_snapshot.json').read_text())
        nodes={k:n for k,n in graph['nodes'].items() if n['selected']}
        for n in nodes.values():
            if not n.get('spec') or n.get('review',{}).get('verdict')!='pass':
                raise ValueError('selected function lacks reviewed spec')
    if input_transition is not None:
        from .input_revision import transition
        inventory, _ = transition(root,source,inventory,input_transition)
    elif snapshot(root)!=inventory:raise ValueError('input differs from stage2 snapshot')
    if status.get("workflow")=="source-bundles-v1" or any(n.get("source_bundle") for n in nodes.values()):
        bundles_from_nodes(source,nodes.values(),inventory)
    return graph,nodes,inventory


GUIDANCE_PATH = Path(__file__).resolve().parents[1] / 'SPECIFICATION_WRITING_GUIDE.md'


def writing_guidance():
    import hashlib
    content = GUIDANCE_PATH.read_text()
    version = hashlib.sha256(content.encode()).hexdigest()
    return {'path':str(GUIDANCE_PATH), 'version':'sha256:' + version,
            'sha256':version, 'content':content}


def upstream_needs(node):
    import copy
    spec = node['spec']
    items = copy.deepcopy(spec.get('common_needs', []))
    return {'present':'common_needs' in spec, 'items':items,
            'ids':['upstream-' + str(i) for i in range(len(items))]}


def planning_index(proposal, extracts):
    if proposal.get('protocol_version') == 3:
        return {'schema_version':3, 'protocol_version':3,
                'candidate_digest':planning.candidate_digest(proposal), 'needs':extracts,
                'references':proposal['references'], 'uses':proposal['uses'],
                'reference_strategies':proposal.get('reference_strategies', []),
                'strategy_search':proposal['strategy_search'],
                'proof_status':'not_proved', 'target_status':'not_validated',
                'execution_status':'not_started'}
    return {'schema_version':2, 'candidate_digest':digest(proposal),
            'needs':extracts, 'references':proposal['references'],
            'reference_strategies':proposal.get('reference_strategies', []),
            'decisions':proposal['coverage'],
            'validation_obligations':{i['id']:i['validation_obligations'] for i in proposal['items']},
            'proof_status':'not_proved', 'execution_status':'not_started'}


def render(proposal, review=None):
    if proposal.get('protocol_version') == 3:
        return render_handoff(proposal, review)

    lines=['# 公共定义与 lemma 候选','','精确数学/自然语言草案；未形式化、未证明。独立审查见 review.json。','']
    for item in proposal['items']:
        lines+=['## '+item['name']+' ('+item['id']+')','']
        for k,title in [('parameters','参数'),('assumptions','前提'),('statement','陈述'),('purpose','用途与共享范围'),('adaptation','参考比较与适配'),('validation_plan','后续交付与检查计划')]:
            lines += [title+'：'+item[k],'']
        lines+=['参考 strategy：'+', '.join(item.get('strategy_ids',[])),'']
        lines+=['依赖：'+', '.join(item['depends_on']),'用于：'+', '.join(item['used_by']),'']
    lines+=['## 覆盖和未决项','','```json',json.dumps({'coverage':proposal['coverage'],'unknowns':proposal['unknowns']},ensure_ascii=False,indent=2),'```','']
    if proposal.get('upstream_conditions'):
        lines+=['## 继承的条件（未证明）','','```json',json.dumps(proposal['upstream_conditions'],ensure_ascii=False,indent=2),'```','']
    lines += ['','## 需求、参考与验证义务记录','',
              '以下为候选规划，未执行验证。','','```json',
              json.dumps({'references':proposal.get('references',[]),
                          'coverage':proposal.get('coverage',{}),
                          'validation_obligations':{i['id']:i.get('validation_obligations',[]) for i in proposal['items']}},
                         ensure_ascii=False,indent=2),'```']
    return '\n'.join(lines)


def render_handoff(proposal, review=None):
    # A review of another candidate or protocol never authorizes a recommendation.
    reviewed = (isinstance(review, dict) and review.get('protocol_version') == 3
                and review.get('candidate_digest') == planning.candidate_digest(proposal))
    refs = {r['id']:r for r in proposal['references']}
    reference_reviews = {r['reference_id']:r for r in review.get('reference_reviews', [])} if reviewed else {}
    use_reviews = {r['use_id']:r for r in review.get('use_reviews', [])} if reviewed else {}
    def accepted(use):
        return (use_reviews.get(use['id'], {}).get('verdict') == 'pass'
                and all(reference_reviews.get(i, {}).get('verdict') == 'pass' for i in use['reference_ids']))
    lines = ['# 参考检索交接', '', '审查状态：' + (review['verdict'] if reviewed else '待审'),
             '目标端验证：未验证；未执行 Coq、QCP 或调用匹配检查。', '']
    for fid in dict.fromkeys(u['function_id'] for u in proposal['uses']):
        lines += ['## 函数 ' + fid, '', '### 可参考清单', '']
        usable = [u for u in proposal['uses'] if u['function_id'] == fid and u['result'] in ('direct', 'adapt', 'idea') and accepted(u)]
        lines += ['- ' + u['id'] + ' / ' + u['need_id'] + '：' + u['purpose'] + '；审查：pass；检索判断：' + u['result'] + '；参考 ' + ', '.join(u['reference_ids']) for u in usable] or ['无已获审查认可的推荐。']
        lines += ['', '### 检索结果、适配限制与待确认事项', '']
        for use in (u for u in proposal['uses'] if u['function_id'] == fid):
            lines += ['- ' + use['id'] + ' / ' + use['need_id'] + '：' + use['result'] + '；审查：' + (use_reviews.get(use['id'], {}).get('verdict', '待审') if reviewed else '待审'),
                      '  用途：' + use['purpose'], '  差异：' + (use.get('adaptation') or '无'),
                      '  待确认：' + (use.get('uncertainty') or '无'), '  已查范围：' + (use.get('search_scope') or '无')]
    lines += ['', '## 共享参考原意及前提', '']
    for ident, ref in refs.items():
        lines += ['### ' + ident + ' — ' + ref['name'], '', '审查：' + reference_reviews.get(ident, {}).get('verdict', '待审') + '（未获认可时不可采用本条解释）', '原意：' + ref['meaning'],
                  '前提：' + str(ref['premises']), '原文位置：' + json.dumps(ref['evidence'], ensure_ascii=False), '']
    lines += ['## Strategy 附件', '', json.dumps({'reference_strategies':proposal.get('reference_strategies', []), 'strategy_search':proposal['strategy_search']}, ensure_ascii=False, indent=2),
              '', '## 审查记录', '', json.dumps(review if reviewed else {'status':'pending'}, ensure_ascii=False, indent=2)]
    return '\n'.join(lines) + '\n'


def requires_revision(review):
    if not review:
        return False
    if review.get('verdict') == 'needs_revision':
        return True
    if review.get('protocol_version') == 3:
        return any(row.get('verdict') == 'needs_revision'
                   for key in ('reference_reviews', 'use_reviews') for row in review.get(key, []))
    return review.get('verdict') == 'partial' and any(
        row.get('action') == 'revise' for row in review.get('item_reviews', []))


def run_pipeline(root, output, source, factory, *, budgets=None, max_revisions=1,
                 resume=False, recover_from=None, max_report_chars=24000, component_review=False, input_transition=None, revise_from=None, label='fixture', model_identity=None, protocol_version=3):
    import fcntl
    if type(protocol_version) is not int or protocol_version not in (2, 3):
        raise ValueError('unsupported pipeline protocol_version')
    if protocol_version == 2 and label != 'fixture':
        raise ValueError('protocol_version=2 is restricted to fixed-response fixture replay')
    root=Path(root).resolve(strict=True); output=Path(output).resolve();source=Path(source).resolve(strict=True)
    if output.is_relative_to(root) or output==source or output.is_relative_to(source):
        raise ValueError('stage3 output must be outside input and upstream run')
    if recover_from is not None and (resume or output.is_relative_to(Path(recover_from).resolve())):
        raise ValueError('recovery requires a new output outside the previous run')
    if max_report_chars is not None and (type(max_report_chars) is not int or max_report_chars<1):
        raise ValueError('max_report_chars must be positive or unlimited')
    if max_revisions<0:raise ValueError('max_revisions must be nonnegative')
    if bool(input_transition)!=bool(revise_from):
        raise ValueError('input-transition and revise-from must be supplied together')
    if revise_from and output.is_relative_to(Path(revise_from).resolve()):
        raise ValueError('input revision requires a separate output')
    graph,nodes,inventory=load_upstream(root,source,input_transition)
    identity={'max_report_chars':max_report_chars,'recovery_policy':1,'strategy_policy':strategies.VERSION,'material_policy':materials.VERSION if protocol_version == 3 else 1,'planning_policy':protocol_version,'writing_guidance_digest':writing_guidance()['sha256'],'prompt_digest':digest({r:prompt(r,{},max_report_chars,component_review) for r in ('extract','common','review')}),'graph_digest':digest(graph),'source':str(source),'condition_policy':1,'model':model_identity or {'mode':label},'mode':label}
    transition_record=None;revision_data=None;revision_record=None
    if component_review:identity['component_policy']=1
    if revise_from:
        from . import input_revision
        old_inventory=json.loads((Path(revise_from)/'input_snapshot.json').read_text())
        manifest=json.loads(Path(input_transition).read_text())
        _,transition_record=input_revision.transition(root,source,snapshot(Path(manifest['baseline_root'])),input_transition)
        current_hashes={r['path']:r['sha256'] for r in inventory}
        if any(current_hashes.get(r['path'])!=r['sha256'] for r in old_inventory):
            raise ValueError('revision changed or removed an earlier input material')
        revision_data,revision_record=input_revision.seed(revise_from,graph,nodes,old_inventory,identity['model'], protocol_version=protocol_version)
        identity['input_transition']=transition_record
        identity['revision_seed']=revision_record
    if not resume:output.mkdir(parents=True,exist_ok=False)
    elif not output.is_dir():raise ValueError('resume directory missing')
    with (output/'run.lock').open('a') as lock:
        try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:raise ValueError('stage3 run already active')
        if resume:
            if json.loads((output/'identity.json').read_text())!=identity:raise ValueError('upstream/model/planning policy changed; use a new output directory')
            data=json.loads((output/'checkpoint.json').read_text());state=json.loads((output/'status.json').read_text())
            if state.get('checkpoint_digest')!=digest(data):raise ValueError('checkpoint/status mismatch')
            if (data.get('candidate') or {}).get('protocol_version') == 3 and data.get('review'):
                if (data['review'].get('protocol_version') != 3 or data['review'].get('candidate_digest') != planning.candidate_digest(data['candidate'])):
                    raise ValueError('checkpoint review belongs to another candidate or protocol')
            if state.get('status')=='common_candidates_reviewed':
                strategies.verify_export(data['candidate'], output)
                return state
        else:
            data={'extracts':{},'candidate':None,'review':None}
            state={'status':'running','attempt':0,'tasks':{},'proof_status':'not_proved','mode':label,'protocol_version':protocol_version,'run_status':'running','review_status':'pending','target_status':'not_validated'}
            write_json(output/'identity.json',identity);write_json(output/'input_snapshot.json',inventory)
            write_json(output/'specification-writing-guidance.json',writing_guidance())
        budgets=budgets or Budgets(calls=24,context_chars=60000)
        recovery_task=None;recovery_record=None
        if recover_from is not None:
            from . import recovery
            data,recovery_task,recovery_record=recovery.prepare(recover_from,identity,inventory,nodes,budgets)
            write_json(output/'recovery.json',recovery_record)
            state['error_history']=recovery_record.get('error_history', [])
            for ident, report in data['extracts'].items():
                folder=output/'functions'/ident;folder.mkdir(parents=True,exist_ok=True)
                write_json(folder/'common_needs.json',report)
            if data.get('candidate') is not None:
                import shutil
                for filename in ('candidate.json','candidate.md','planning.json'):
                    shutil.copyfile(Path(recover_from)/filename,output/filename)
                shutil.copytree(Path(recover_from)/'reference_strategies',output/'reference_strategies')
        if revision_data is not None and not resume and recover_from is None:
            data=revision_data;data['needs_input_revision']=True
            write_json(output/'input-transition.json',transition_record)
            write_json(output/'revision-seed.json',revision_record)
            write_json(output/'previous-candidate.json',data['candidate'])
            write_json(output/'previous-review.json',data['review'])
            for ident,report in data['extracts'].items():
                folder=output/'functions'/ident;folder.mkdir(parents=True,exist_ok=True)
                write_json(folder/'common_needs.json',report)
        upstream_context=graph.get('upstream_context',{'kind':'legacy_reviewed_candidates','semantic_review':True,'proved':False})
        state['upstream_context']=upstream_context
        state.setdefault('error_history', [])
        write_json(output/'upstream_context.json',upstream_context)
        write_json(output/'upstream_conditions.json',contracts.upstream_conditions(nodes))
        budgets=budgets or Budgets(calls=24,context_chars=60000)
        from stage3.read_materials import SourcePreparation
        source_preparation=SourcePreparation(root)
        def save():
            write_json(output/'checkpoint.json',data)
            state['checkpoint_digest']=digest(data)
            state['expected_functions']=list(nodes)
            state['extracted_functions']=list(data['extracts'])
            write_json(output/'status.json',state)
        def record_error(reason):
            entry = {'reason':reason, 'status':state.get('status'), 'attempt':state['attempt']}
            if not state['error_history'] or state['error_history'][-1].get('reason') != reason or state['error_history'][-1].get('attempt') != state['attempt']:
                state['error_history'].append(entry)
            state['reason'] = reason
        def execute(role,assignment,artifacts,validator):
            nonlocal recovery_task
            state['attempt']+=1;save();tid=role+'-'+str(state['attempt']).zfill(4)
            scoped=None
            selected_nodes=[nodes[assignment['function']['id']]] if role=='extract' else list(nodes.values())
            if any(n.get('source_bundle') for n in nodes.values()):
                scoped=bundles_from_nodes(source,selected_nodes,inventory)
                artifacts=dict(artifacts)
                artifacts['source-index']=[{'function_id':m['function_id'],'ranges':[x['original'] for x in m['mappings']]} for _,m in scoped]
            artifacts = dict(artifacts)
            artifacts['specification-writing-guidance'] = writing_guidance()
            if artifacts['specification-writing-guidance']['sha256'] != identity['writing_guidance_digest']:
                raise ValueError('specification writing guidance changed during run')
            instructions=('Report protocol_version must be ' + str(protocol_version) + '. First read artifact specification-writing-guidance at ' + str(GUIDANCE_PATH) + '; use its recorded version and requirements. This trusted artifact does not expand Reader permissions.\n' + prompt(role,assignment,max_report_chars,component_review))
            if scoped is not None:instructions='Reader only exposes extracted source copies at original coordinates. Read source-index for exact available ranges. Missing material must remain unknown/insufficient; no original repository fallback.\n'+instructions
            if scoped is not None and any(m.get('source_kind')=='reviewed_preparation' for _,m in scoped):
                instructions='Sources are human-reviewed adapted input in prepared/ coordinates, NOT verbatim original-library evidence. Callee declarations and QCP contracts are preprocessed interfaces in the same C file; do not infer their implementations or promote imported contract status into a new proof.\n'+instructions
            task_artifacts, mandatory = materials.prepare(role, graph,
                {n['id']:n for n in selected_nodes}, upstream_context, artifacts, scoped, source_preparation,
                protocol_version=protocol_version)
            mandatory = ([{'tool':'artifact', 'id':'specification-writing-guidance'}]
                         + [action for action in mandatory if action != {'tool':'artifact', 'id':'specification-writing-guidance'}])
            resumed=recovery_task
            if resumed is not None and recovery_record['role']!=role:
                raise ValueError('recovery task role does not match next pipeline step')
            if transition_record is not None:
                from stage1.reader import Reader
                transition_reader=Reader(root,output/'unused-transition-read-log')
                for entry in transition_record['manifest']['added_files']:
                    lines,_=transition_reader.lines(entry['path'])
                    mandatory.extend({'tool':'read','path':entry['path'],'start':i,'count':min(120,len(lines)-i+1)}
                                     for i in range(1,len(lines)+1,120))
                task_artifacts['input-transition']=transition_record
                mandatory.insert(0,{'tool':'artifact','id':'input-transition'})
            def versioned_validator(report, reader, reads):
                actual = report.get('protocol_version', 2) if isinstance(report, dict) else None
                if actual != protocol_version:
                    return ['report protocol_version must match pipeline protocol ' + str(protocol_version)]
                return validator(report, reader, reads)
            task_reader_factory = reader_factory(scoped) if scoped is not None else None
            if protocol_version == 3:
                from .read_cost import reader_factory as deduplicating_reader_factory
                task_reader_factory = deduplicating_reader_factory(task_reader_factory)
            result=run_task(root,output/'tasks'/tid,factory(role,tid),instructions,versioned_validator,
                            role=role,task_id=tid,budgets=budgets,artifacts=task_artifacts,label=label,allow_report_patch=True,required_inputs=mandatory,
                            reader_factory=task_reader_factory,
                            resume_from=resumed, resume_revalidate=bool(resumed and recovery_record['revalidate_saved_report']),
                            resume_prompt_migration=({'old_max_report_chars':recovery_record['old_report_limit'],
                                'new_max_report_chars':max_report_chars} if resumed and recovery_record['old_report_limit']!=max_report_chars else None),
                            complete_bundle_evidence=True)
            if resumed is not None:
                recovery.recheck(recovery_record)
                recovery_task=None
            state['tasks'][tid]={k:result.get(k) for k in ('status','reason','calls','elapsed_seconds')}
            current_graph,_,_=load_upstream(root,source,input_transition)
            if revision_record is not None:
                from .recovery import recheck
                recheck(revision_record)
            if digest(current_graph)!=identity['graph_digest']:
                raise ValueError('upstream changed during stage3')
            if result['status']!='task_completed':
                state.update(status='incomplete',run_status='incomplete')
                record_error('task did not complete: ' + tid + ': ' + str(result.get('reason', 'unknown')))
                save();return None
            return result['report']
        try:
            if state.get('reason'):
                record_error(state['reason'])
                state.pop('reason', None)
            state.update(status='running',run_status='running');save()
            for ident,node in nodes.items():
                if ident in data['extracts']:continue
                report=execute('extract',{'function':{k:node[k] for k in ('id','symbol','source','configuration')}},
                    {'spec':node['spec'], 'upstream-needs':upstream_needs(node)},partial(contracts.extraction,node=node,max_report_chars=max_report_chars))
                if report is None:return state
                report['upstream_needs']=upstream_needs(node)
                data['extracts'][ident]=report;save()
                folder=output/'functions'/ident;folder.mkdir(parents=True,exist_ok=True)
                write_json(folder/'common_needs.json',report)
            artifacts={'spec:'+k:n['spec'] for k,n in nodes.items()}
            artifacts.update({'extract:'+k:v for k,v in data['extracts'].items()})
            assignment={'functions':list(nodes),'selection':graph['selection_inventory']['selection'],
                        'scope':'All selected functions; upstream specs are immutable reference material, not proved.'}
            for revision in range(max_revisions+1):
                if data.get('needs_input_revision') or data['candidate'] is None or requires_revision(data['review']):
                    inputs=dict(artifacts)
                    if data['candidate']:inputs['previous_candidate']=data['candidate']
                    if data['review']:inputs['revision_review']=data['review']
                    report=execute('common',assignment,inputs,partial(contracts.candidate,nodes=nodes,extracts=data['extracts'],max_report_chars=max_report_chars))
                    if report is None:return state
                    scoped_export = (bundles_from_nodes(source, list(nodes.values()), inventory)
                                     if any(n.get('source_bundle') for n in nodes.values()) else None)
                    from stage1.reader import Reader
                    export_reader = (reader_factory(scoped_export) if scoped_export is not None else Reader)(root, output/'strategy-export-reads.jsonl')
                    strategies.export(report, export_reader, output)
                    if data.get('candidate') is not None:
                        before={i['id']:i for i in data['candidate'].get('uses', data['candidate'].get('items', []))}
                        after={i['id']:i for i in report.get('uses', report.get('items', []))}
                        write_json(output/('candidate-change-'+str(state['attempt'])+'.json'), {
                            'previous_digest':digest(data['candidate']),'candidate_digest':digest(report),
                            'added':sorted(set(after)-set(before)),'removed':sorted(set(before)-set(after)),
                            'changed':sorted(i for i in before.keys() & after.keys() if before[i]!=after[i]),
                            'unchanged':sorted(i for i in before.keys() & after.keys() if before[i]==after[i]),
                            'note':'Structural comparison only; all candidates are independently reviewed again.'})
                    (output/'review.json').unlink(missing_ok=True)
                    data['candidate']=report;data['review']=None;state['review_status']='pending';data.pop('needs_input_revision',None);save()
                    write_json(output/'planning.json',planning_index(report, data['extracts']))
                    write_json(output/'candidate.json',report);write_text(output/'candidate.md',render(report))
                result=execute('review',assignment,{**artifacts,'candidate':data['candidate']},
                    partial(contracts.review,proposal=data['candidate'],nodes=nodes,max_report_chars=max_report_chars,component_review=component_review))
                if result is None:return state
                data['review']=result;state['review_status']=result['verdict'];save();write_json(output/'review.json',result)
                write_text(output/'candidate.md',render(data['candidate'],result))
                if not requires_revision(result):break
            state['status']='common_candidates_reviewed' if data['review']['verdict']=='pass' else data['review']['verdict']
            state.update(run_status='completed',review_status=data['review']['verdict'],target_status='not_validated')
            state.pop('reason',None)
            save()
            write_text(output/'SUMMARY.md','# 阶段四结果\n\n状态：'+state['status']+'\n\n覆盖 '+str(len(nodes))+' 个函数；已证明库共享参考 '+str(len(data['candidate'].get('references', data['candidate'].get('items', []))))+' 项。目标端适用性未验证。\n\n当前审查：'+state['review_status']+'；目标端验证：未验证。\n')
            return state
        except (Exception,KeyboardInterrupt) as exc:
            state.update(status='interrupted' if isinstance(exc,KeyboardInterrupt) else 'incomplete',run_status='incomplete')
            record_error(str(exc));save()
            if isinstance(exc,KeyboardInterrupt):raise
            return state
