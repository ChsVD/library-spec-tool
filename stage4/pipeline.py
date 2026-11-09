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


def render(proposal):
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


def run_pipeline(root, output, source, factory, *, budgets=None, max_revisions=1,
                 resume=False, recover_from=None, max_report_chars=24000, component_review=False, input_transition=None, revise_from=None, label='fixture', model_identity=None):
    import fcntl
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
    identity={'max_report_chars':max_report_chars,'recovery_policy':1,'strategy_policy':strategies.VERSION,'material_policy':materials.VERSION,'planning_policy':planning.VERSION,'prompt_digest':digest({r:prompt(r,{},max_report_chars,component_review) for r in ('extract','common','review')}),'graph_digest':digest(graph),'source':str(source),'condition_policy':1,'model':model_identity or {'mode':label},'mode':label}
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
        revision_data,revision_record=input_revision.seed(revise_from,graph,nodes,old_inventory,identity['model'])
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
            if state.get('status')=='common_candidates_reviewed':
                strategies.verify_export(data['candidate'], output)
                return state
        else:
            data={'extracts':{},'candidate':None,'review':None}
            state={'status':'running','attempt':0,'tasks':{},'proof_status':'not_proved','mode':label}
            write_json(output/'identity.json',identity);write_json(output/'input_snapshot.json',inventory)
        budgets=budgets or Budgets(calls=24,context_chars=60000)
        recovery_task=None;recovery_record=None
        if recover_from is not None:
            from . import recovery
            data,recovery_task,recovery_record=recovery.prepare(recover_from,identity,inventory,nodes,budgets)
            write_json(output/'recovery.json',recovery_record)
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
        def execute(role,assignment,artifacts,validator):
            nonlocal recovery_task
            state['attempt']+=1;save();tid=role+'-'+str(state['attempt']).zfill(4)
            scoped=None
            selected_nodes=[nodes[assignment['function']['id']]] if role=='extract' else list(nodes.values())
            if any(n.get('source_bundle') for n in nodes.values()):
                scoped=bundles_from_nodes(source,selected_nodes,inventory)
                artifacts=dict(artifacts)
                artifacts['source-index']=[{'function_id':m['function_id'],'ranges':[x['original'] for x in m['mappings']]} for _,m in scoped]
            instructions=prompt(role,assignment,max_report_chars,component_review)
            if scoped is not None:instructions='Reader only exposes extracted source copies at original coordinates. Read source-index for exact available ranges. Missing material must remain unknown/insufficient; no original repository fallback.\n'+instructions
            if scoped is not None and any(m.get('source_kind')=='reviewed_preparation' for _,m in scoped):
                instructions='Sources are human-reviewed adapted input in prepared/ coordinates, NOT verbatim original-library evidence. Callee declarations and QCP contracts are preprocessed interfaces in the same C file; do not infer their implementations or promote imported contract status into a new proof.\n'+instructions
            task_artifacts, mandatory = materials.prepare(role, graph,
                {n['id']:n for n in selected_nodes}, upstream_context, artifacts, scoped, source_preparation)
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
            result=run_task(root,output/'tasks'/tid,factory(role,tid),instructions,validator,
                            role=role,task_id=tid,budgets=budgets,artifacts=task_artifacts,label=label,allow_report_patch=True,required_inputs=mandatory,
                            reader_factory=reader_factory(scoped) if scoped is not None else None,
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
                state.update(status='incomplete',reason='task did not complete: '+tid);save();return None
            return result['report']
        try:
            state['status']='running';save()
            for ident,node in nodes.items():
                if ident in data['extracts']:continue
                report=execute('extract',{'function':{k:node[k] for k in ('id','symbol','source','configuration')}},
                    {'spec':node['spec']},partial(contracts.extraction,node=node,max_report_chars=max_report_chars))
                if report is None:return state
                data['extracts'][ident]=report;save()
                folder=output/'functions'/ident;folder.mkdir(parents=True,exist_ok=True)
                write_json(folder/'common_needs.json',report)
            artifacts={'spec:'+k:n['spec'] for k,n in nodes.items()}
            artifacts.update({'extract:'+k:v for k,v in data['extracts'].items()})
            assignment={'functions':list(nodes),'selection':graph['selection_inventory']['selection'],
                        'scope':'All selected functions; upstream specs are immutable reference material, not proved.'}
            for revision in range(max_revisions+1):
                if data.get('needs_input_revision') or data['candidate'] is None or (data['review'] and (data['review']['verdict']=='needs_revision' or (data['review']['verdict']=='partial' and any(r.get('action')=='revise' for r in data['review'].get('item_reviews',[]))))):
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
                        before={i['id']:i for i in data['candidate']['items']}
                        after={i['id']:i for i in report['items']}
                        write_json(output/('candidate-change-'+str(state['attempt'])+'.json'), {
                            'previous_digest':digest(data['candidate']),'candidate_digest':digest(report),
                            'added':sorted(set(after)-set(before)),'removed':sorted(set(before)-set(after)),
                            'changed':sorted(i for i in before.keys() & after.keys() if before[i]!=after[i]),
                            'unchanged':sorted(i for i in before.keys() & after.keys() if before[i]==after[i]),
                            'note':'Structural comparison only; all candidates are independently reviewed again.'})
                    data['candidate']=report;data['review']=None;data.pop('needs_input_revision',None);save()
                    write_json(output/'planning.json',{'schema_version':planning.VERSION,'candidate_digest':digest(report),
                        'needs':data['extracts'],'references':report['references'],
                        'reference_strategies':report.get('reference_strategies',[]),
                        'decisions':report['coverage'],
                        'validation_obligations':{i['id']:i['validation_obligations'] for i in report['items']},
                        'proof_status':'not_proved','execution_status':'not_started'})
                    write_json(output/'candidate.json',report);write_text(output/'candidate.md',render(report))
                result=execute('review',assignment,{**artifacts,'candidate':data['candidate']},
                    partial(contracts.review,proposal=data['candidate'],nodes=nodes,max_report_chars=max_report_chars,component_review=component_review))
                if result is None:return state
                data['review']=result;save();write_json(output/'review.json',result)
                if result['verdict']!='needs_revision' and not (result['verdict']=='partial' and any(r.get('action')=='revise' for r in result.get('item_reviews',[]))):break
            state['status']='common_candidates_reviewed' if data['review']['verdict']=='pass' else data['review']['verdict']
            save()
            write_text(output/'SUMMARY.md','# 阶段 3 结果\n\n状态：'+state['status']+'\n\n覆盖 '+str(len(nodes))+' 个函数；公共候选 '+str(len(data['candidate']['items']))+' 项。自然规约及公共内容均未证明。\n')
            return state
        except (Exception,KeyboardInterrupt) as exc:
            state.update(status='interrupted' if isinstance(exc,KeyboardInterrupt) else 'incomplete',reason=str(exc));save()
            if isinstance(exc,KeyboardInterrupt):raise
            return state
