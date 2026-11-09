"""Continue a saved legacy reading without rerunning its module workers."""
import argparse
from functools import partial
import hashlib
import json
from pathlib import Path
from .runner import snapshot
from .reader import Reader
from .contracts import validate_module, check_evidence, require_artifacts, nonempty
from .focused_contracts import (validate_graph_plan, dependency_frontier, validate_selection,
                                validate_screening, validate_pair, validate_focused_review)
from .focused import prompt, card, readable, graph_markdown
from .task import Budgets, run_task, write_json, write_text
from .model_factory import ModelConfig, create_model, model_factory


def load_saved(root, prior):
    root, prior = Path(root), Path(prior)
    if snapshot(root) != json.loads((prior/'input_snapshot.json').read_text()):
        raise ValueError('Input differs from saved reading; cannot reuse')
    plan=json.loads((prior/'plan.json').read_text())
    modules={}; manifest=[]
    for assigned in plan['modules']:
        ident=assigned['id']; path=prior/'modules'/(ident+'.json')
        report=json.loads(path.read_text())
        candidates=[]
        for p in (prior/'tasks').glob('*/status.json'):
            s=json.loads(p.read_text())
            if s.get('status')=='task_completed' and s.get('role')=='module' and s.get('report')==report:
                candidates.append(p.parent)
        if not candidates: raise ValueError('No accepted task for saved module '+ident)
        task=candidates[-1]
        if json.loads((task/'report.json').read_text()) != report:
            raise ValueError('Saved module differs from accepted report')
        reader=Reader(root,prior/'unused-replay-log.jsonl')
        # Replay only feedback actually delivered to the old model, never withheld reads.
        for line in (task/'conversation.jsonl').read_text().splitlines():
            msg=json.loads(line)
            if msg.get('role')!='user': continue
            try: d=json.loads(msg['content'])
            except (ValueError,TypeError): continue
            if isinstance(d,dict) and 'sha256' in d and isinstance(d.get('lines'),list) and d.get('path'):
                real=reader.path(d['path']).relative_to(reader.root).as_posix()
                actual,digest=reader.lines(real)
                if digest!=d['sha256']: raise ValueError('Source evidence changed')
                for item in d['lines']:
                    n=item['line']
                    if actual[n-1]!=item['text']: raise ValueError('Delivered source text mismatch')
                    reader.reads.setdefault(real,[]).append((n,n,digest))
        errors=validate_module(report,reader,set(),task=assigned)
        if errors: raise ValueError(ident+': '+str(errors))
        modules[ident]=report
        manifest.append({'id':ident,'source_report':str(path.resolve()),'source_task':str(task.resolve()),
                         'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                         'validation':'accepted legacy report and delivered original evidence replayed; not independent semantic approval'})
    return plan,modules,manifest


def replay_task_reader(root, task, output):
    reader=Reader(root,output/'unused-evidence-replay.jsonl')
    for line in (task/'conversation.jsonl').read_text().splitlines():
        message=json.loads(line)
        if message.get('role')!='user':continue
        try:d=json.loads(message['content'])
        except (ValueError,TypeError):continue
        if isinstance(d,dict) and 'sha256' in d and isinstance(d.get('lines'),list):
            real=reader.path(d['path']).relative_to(reader.root).as_posix()
            lines,digest=reader.lines(real)
            if digest!=d['sha256']:raise ValueError('Replay evidence changed')
            for item in d['lines']:
                n=item['line']
                if lines[n-1]!=item['text']:raise ValueError('Replay source text mismatch')
                reader.reads.setdefault(real,[]).append((n,n,digest))
    return reader


def validate_conditional_selection(report,reader,reads,*,plan,frontier):
    if not isinstance(report,dict) or report.get('status')!='tentative':
        return validate_selection(report,reader,reads,plan=plan,frontier=frontier)
    errors=require_artifacts(reads,{'plan','dependency_frontier'})
    primary=report.get('primary')
    targets={m['id']:m for m in plan['modules'] if m['library']=='openssl'}
    if not isinstance(primary,str) or primary not in targets:
        return errors+['tentative selection must identify a target module']
    for field in ('rationale','scope','blockers','dependency_conditions'):
        if not nonempty(report.get(field)): errors.append(field+' required for tentative selection')
    errors+=check_evidence(report.get('evidence'),reader,libraries={'openssl'})
    errors+=check_evidence(targets[primary]['evidence'],reader)
    return errors


def run(root,prior,output,model_factory,budgets,graph_checkpoint=None,downstream_from=None,comparisons_from=None,review_resume_from=None):
    root,prior,output=Path(root).resolve(),Path(prior).resolve(),Path(output).resolve()
    if output.is_relative_to(root) or output==prior or output.is_relative_to(prior):
        raise ValueError('Continuation must use a separate output directory outside input and prior run')
    old,modules,manifest=load_saved(root,prior)
    output.mkdir(parents=True,exist_ok=False)
    inventory=snapshot(root)
    write_json(output/'input_snapshot.json',inventory); write_json(output/'reuse_manifest.json',manifest)
    state={'status':'running','workflow':'continue_saved_modules_v1','source_run':str(prior),'tasks':{},
           'user_approved':False,'reused_modules':list(modules),'selected_module':None}
    def persist(): write_json(output/'status.json',state)
    def save(name,value,title):
        write_json(output/(name+'.json'),value); readable(output/(name+'.md'),title,value)
    def stop(reason,status='incomplete'):
        state.update(status=status,reason=reason); persist(); return state
    def task(role,ident,validator,assignment,artifacts,extra='',restricted=False):
        resume = Path(review_resume_from)/'tasks'/ident if review_resume_from and role=='review' else None
        if resume and not resume.exists():resume=None
        task_prompt=(resume/'task.md').read_text().split('\n\nTask budgets:')[0] if resume else prompt(role,assignment)+'\n'+extra
        result=run_task(root,output/'tasks'/ident,model_factory(role,ident),task_prompt,
                        validator,role=role,task_id=ident,budgets=budgets,artifacts=artifacts,label='real_codex',
                        allowed_tools={'artifact','draft','checkpoint','finish'} if restricted else None,
                        resume_from=resume,backend_retries=1)
        state['tasks'][ident]={k:result.get(k) for k in ('status','reason','calls','elapsed_seconds')}; persist()
        return result
    persist()
    compact={'coverage':old['coverage'],'modules':[{**m,
        'previous_responsibilities_and_boundary':modules[m['id']]['sections']['模块职责与边界'],
        'previous_dependencies':modules[m['id']]['sections']['对外依赖与使用关系'],
        'previous_evidence':modules[m['id']]['evidence']} for m in old['modules']]}
    def graph_validate(report,reader,reads):
        errors=validate_graph_plan(report,reader,reads,max_modules=len(modules))
        errors+=require_artifacts(reads,{'previous_map'})
        if isinstance(report,dict) and isinstance(report.get('modules'),list):
            if {m.get('id') for m in report['modules'] if isinstance(m,dict)}!=set(modules): errors.append('Preserve all previous module IDs')
            original={m['id']:m for m in old['modules']}
            for m in report['modules']:
                if isinstance(m,dict) and m.get('id') in original:
                    for field in ('library','scope'):
                        if m.get(field)!=original[m['id']][field]:errors.append('Preserve previous '+field+' for '+m['id'])
        return errors
    try:
        if downstream_from:
            previous=Path(downstream_from).resolve()
            if snapshot(root)!=json.loads((previous/'input_snapshot.json').read_text()):raise ValueError('Downstream input changed')
            plan=json.loads((previous/'plan.json').read_text())
            frontier=dependency_frontier(plan)
            provenance=json.loads((previous/'graph_provenance.json').read_text())
            base_checkpoint=Path(provenance['base_checkpoint'])
            if hashlib.sha256(base_checkpoint.read_bytes()).hexdigest()!=provenance['base_sha256']:raise ValueError('Base graph changed')
            base_graph=json.loads(base_checkpoint.read_text())['content']
            repair_task=previous/'tasks'/provenance['repair_task']
            repair_status=json.loads((repair_task/'status.json').read_text())
            patch=json.loads((repair_task/'report.json').read_text())
            if repair_status.get('status')!='task_completed' or repair_status.get('report')!=patch:raise ValueError('Graph repair not accepted')
            by_id={m['id']:m for m in patch['modules']}
            expected_plan={'coverage':{**base_graph['coverage'],'mini-gmp':patch['coverage_mini_gmp']},
                           'modules':[by_id.get(m['id'],m) for m in base_graph['modules']],
                           'evidence':base_graph['evidence']+patch['evidence']}
            if expected_plan!=plan:raise ValueError('Merged graph changed')
            combined=replay_task_reader(root,base_checkpoint.parent.parent,output)
            fresh=replay_task_reader(root,repair_task,output)
            for path,ranges in fresh.reads.items():combined.reads.setdefault(path,[]).extend(ranges)
            errors=graph_validate(plan,combined,{'previous_map'})
            if errors:raise ValueError(str(errors))
            def accepted(name,validator):
                report=json.loads((previous/(name+'.json')).read_text())
                task_dir=previous/'tasks'/name
                status=json.loads((task_dir/'status.json').read_text())
                if status.get('status')!='task_completed' or status.get('report')!=report or json.loads((task_dir/'report.json').read_text())!=report:raise ValueError(name+' not accepted')
                errors=validator(report,replay_task_reader(root,task_dir,output),set(status.get('artifact_reads',[])))
                if errors:raise ValueError(name+str(errors))
                return report
            selection=accepted('selection',partial(validate_conditional_selection,plan=plan,frontier=frontier))
            if selection['status']=='unable':return stop('no_supported_target','needs_revision')
            target=next(m for m in plan['modules'] if m['id']==selection['primary'])
            refs=[m for m in plan['modules'] if m['library']!='openssl']
            screening=accepted('screening',partial(validate_screening,target=target,references=refs))
            matches={c['reference'] for c in screening['candidates'] if c['decision']=='match'}
            selected=[target]+[m for m in refs if m['id'] in matches]
            common={'plan':plan,'dependency_frontier':frontier}
            for name,value in [('plan',plan),('dependency_frontier',frontier),('selection',selection),('screening',screening)]:save(name,value,'复用已核验的'+name)
            write_json(output/'dependency_graph.json',{'nodes':[m['id'] for m in plan['modules']],'edges':[{'dependent':m['id'],**e} for m in plan['modules'] for e in m['dependencies']],'frontier':frontier})
            graph_markdown(plan,frontier,output/'dependency_graph.md')
            write_json(output/'graph_provenance.json',provenance)
            write_json(output/'downstream_provenance.json',{'source_run':str(previous),'reused':['plan','selection','screening'],'evidence_replayed':True})
            state['selected_module']=selection['primary'];state['downstream_from']=str(previous);persist()
            (output/'modules').mkdir()
            from .multi import module_markdown
            for m in selected:
                write_json(output/'modules'/(m['id']+'.json'),modules[m['id']]);module_markdown(modules[m['id']],output/'modules'/(m['id']+'.md'))
        else:
            if graph_checkpoint is None:
                result=task('planner','dependency-supplement',graph_validate,{'existing_modules':list(modules)},
                    {'previous_map':compact},'本次是续接，不重新划分或深读24个模块。先读previous_map，其中职责、依赖和引用来自已保存报告，是解释不是本角色原文证据。保持所有模块ID、library和原范围，补齐卡片与依赖图；沿旧引用定向核对少量关键原文，输出新契约。不能为选出叶子删去调用、共享表示、外部或循环依赖。图可能无eligible，这也是有效结果；后续可提出有条件的缩小范围建议。每个节点与边引用本角色确实收到的read区间。')
                if result['status']!='task_completed': return stop('dependency_supplement_'+result['status'])
                plan=result['report']; save('plan',plan,'既有模块的依赖补充')
            else:
                checkpoint=Path(graph_checkpoint).resolve()
                prior_task=checkpoint.parent.parent
                prior_graph_run=prior_task.parent.parent
                if snapshot(root)!=json.loads((prior_graph_run/'input_snapshot.json').read_text()):
                    raise ValueError('Graph checkpoint input changed')
                candidate=json.loads(checkpoint.read_text())['content']
                graph_reader=Reader(root,output/'unused-graph-replay.jsonl')
                for line in (prior_task/'conversation.jsonl').read_text().splitlines():
                    msg=json.loads(line)
                    if msg.get('role')!='user':continue
                    try:d=json.loads(msg['content'])
                    except (ValueError,TypeError):continue
                    if isinstance(d,dict) and 'sha256' in d and isinstance(d.get('lines'),list):
                        real=graph_reader.path(d['path']).relative_to(graph_reader.root).as_posix()
                        lines,digest=graph_reader.lines(real)
                        if digest!=d['sha256']:raise ValueError('Prior graph evidence changed')
                        for item in d['lines']:
                            n=item['line']
                            if lines[n-1]!=item['text']:raise ValueError('Prior graph text changed')
                            graph_reader.reads.setdefault(real,[]).append((n,n,digest))
                repair_ids={m['id'] for m in candidate['modules'] if m['library']=='mini-gmp'}
                def merge_patch(patch):
                    replacements={m['id']:m for m in patch['modules']}
                    return {'coverage':{**candidate['coverage'],'mini-gmp':patch['coverage_mini_gmp']},
                            'modules':[replacements.get(m['id'],m) for m in candidate['modules']],
                            'evidence':candidate['evidence']+patch['evidence']}
                def validate_patch(patch,reader,reads):
                    if not isinstance(patch,dict) or not isinstance(patch.get('modules'),list):return ['modules list required']
                    if {m.get('id') for m in patch['modules']}!=repair_ids:return ['Patch only the two mini-gmp nodes']
                    errors=require_artifacts(reads,{'repair_input'})
                    for m in patch['modules']:
                        errors+=check_evidence(m.get('evidence'),reader,libraries={'mini-gmp'})
                        for e in m.get('dependencies',[]):errors+=check_evidence(e.get('evidence'),reader,libraries={'mini-gmp'})
                    errors+=check_evidence(patch.get('evidence'),reader,libraries={'mini-gmp'})
                    combined_reader=Reader(root,output/'unused-composite-log.jsonl')
                    combined_reader.reads={p:list(v) for p,v in graph_reader.reads.items()}
                    for p,v in reader.reads.items():combined_reader.reads.setdefault(p,[]).extend(v)
                    errors+=graph_validate(merge_patch(patch),combined_reader,{'previous_map'})
                    return errors
                result=task('planner','dependency-repair-mini-gmp',validate_patch,
                    {'module_ids':sorted(repair_ids)},
                    {'repair_input':{'candidate_nodes':[m for m in candidate['modules'] if m['id'] in repair_ids],
                                     'old_module_reports':[modules[i] for i in sorted(repair_ids)]}},
                    '仅补前序依赖图的mini-gmp两个节点，其他22节点不改动、不重读。先读repair_input，再定向核对原文。保持ID、library、scope。输出契约改为 {modules:[两个完整节点，字段同planner模块卡片],coverage_mini_gmp:{mapped_areas,unread_areas,configuration_unknowns},evidence:[本角色独立原文引用]}。所有新节点和边引用必须本角色read，旧报告只是线索。短范围核对即可，依赖不完整可明确unknown，不重写完整模块说明。')
                if result['status']!='task_completed':return stop('dependency_repair_'+result['status'])
                plan=merge_patch(result['report']);save('plan',plan,'补齐证据后的依赖图规划')
                write_json(output/'graph_provenance.json',{'base_checkpoint':str(checkpoint),
                    'base_sha256':hashlib.sha256(checkpoint.read_bytes()).hexdigest(),
                    'retained_nodes':[m['id'] for m in candidate['modules'] if m['id'] not in repair_ids],
                    'replaced_nodes':sorted(repair_ids),'repair_task':'dependency-repair-mini-gmp',
                    'validation':'composite source evidence replay; new node evidence independently read by repair task'})
            frontier=dependency_frontier(plan); save('dependency_frontier',frontier,'依赖候选与阻断')
            write_json(output/'dependency_graph.json',{'nodes':[m['id'] for m in plan['modules']], 'edges':[{'dependent':m['id'],**e} for m in plan['modules'] for e in m['dependencies']], 'frontier':frontier})
            graph_markdown(plan,frontier,output/'dependency_graph.md')
            common={'plan':plan,'dependency_frontier':frontier}
            result=task('selection','selection',partial(validate_conditional_selection,plan=plan,frontier=frontier),{},common,
                '续接选择规则：优先按eligible给proposed。若整模块因循环或公共运行库依赖均被阻断，可以输出status=tentative，明确primary、scope中的首轮函数/子范围和dependency_conditions（哪些条件尚未证明，哪些不在该子范围使用），blockers不得省略。需独立核对这些范围原文。tentative只允许继续研究参考，不表示可开始证明或允许信任未证明前提。若不能合理收窄则unable。不得为了得到推荐修改图或忽略依赖。此条件选择规则覆盖前述只能选eligible的通用限制。')
            if result['status']!='task_completed': return stop('selection_'+result['status'])
            selection=result['report']; save('selection',selection,'下一模块建议及先决条件')
            if selection['status']=='unable': return stop('no_supported_target','needs_revision')
            state['selected_module']=selection['primary'];persist()
            target=next(m for m in plan['modules'] if m['id']==selection['primary']); refs=[m for m in plan['modules'] if m['library']!='openssl']
            result=task('screening','screening',partial(validate_screening,target=target,references=refs),{'target':target['id']},{'card:'+m['id']:card(m) for m in [target]+refs},restricted=True)
            if result['status']!='task_completed': return stop('screening_'+result['status'])
            screening=result['report'];save('screening',screening,'职责与边界初筛')
            matches={c['reference'] for c in screening['candidates'] if c['decision']=='match'}
            selected=[target]+[m for m in refs if m['id'] in matches]
            (output/'modules').mkdir()
            from .multi import module_markdown
            for m in selected:
                write_json(output/'modules'/(m['id']+'.json'),modules[m['id']]);module_markdown(modules[m['id']],output/'modules'/(m['id']+'.md'))
        comparisons=[];(output/'comparisons').mkdir();(output/'reviews').mkdir()
        for ref in selected[1:]:
            cache_source=Path(comparisons_from or downstream_from) if (comparisons_from or downstream_from) else None
            if cache_source and not (cache_source/'tasks'/('comparison-'+ref['id'])/'report.json').exists():
                cache_source=Path(downstream_from) if downstream_from else None
            cached=cache_source/'comparisons'/(ref['id']+'.json') if cache_source else None
            if cached and cached.exists():
                saved=json.loads(cached.read_text()); task_dir=cache_source/'tasks'/('comparison-'+ref['id'])
                saved_status=json.loads((task_dir/'status.json').read_text())
                if saved_status.get('status')!='task_completed' or saved_status.get('report')!=saved or json.loads((task_dir/'report.json').read_text())!=saved:raise ValueError('Cached comparison is not accepted')
                errors=validate_pair(saved,replay_task_reader(root,task_dir,output),set(saved_status.get('artifact_reads',[])),target=target,reference=ref)
                if errors:raise ValueError(str(errors))
                comparisons.append(saved);save('comparisons/'+ref['id'],saved,'复用已完成的定向比较')
                state.setdefault('reused_comparisons',[]).append(ref['id']);persist();continue
            pair_artifacts={'selection':selection,'screening':{'target':target['id'],'candidates':[c for c in screening['candidates'] if c['reference']==ref['id']]},'module:'+target['id']:modules[target['id']],'module:'+ref['id']:modules[ref['id']]}
            result=task('comparison','comparison-'+ref['id'],partial(validate_pair,target=target,reference=ref),{'target':target['id'],'reference':ref['id'],'comparison_id':'pair-'+ref['id']},pair_artifacts,
                '复用旧模块说明，不重新生成模块报告。当前选择可能为tentative，请针对scope判断适用性并保留未解决依赖；必要原文可定向补读，不能将有条件推荐写成已可证明。发现选择/图与原文冲突必须写在unknowns和dependencies并说明阻断。')
            if result['status']!='task_completed': return stop('comparison_'+ref['id']+'_'+result['status'])
            comparisons.append(result['report']);save('comparisons/'+ref['id'],result['report'],'定向跨库比较')
        reviews=[]
        for ref in selected[1:] or [None]:
            scope=[modules[target['id']]]+([modules[ref['id']]] if ref else [])
            pairs=[c for c in comparisons if ref and c['reference']==ref['id']]
            artifacts={**common,'selection':selection,'screening':screening,**{'module:'+m['id']:m for m in scope},**{'comparison:'+c['id']:c for c in pairs}}
            ident='review-'+(ref['id'] if ref else target['id'])
            result=task('review',ident,partial(validate_focused_review,plan=plan,selection=selection,screening=screening,modules=scope,comparisons=pairs),{'coverage_checked':[m['id'] for m in scope]},artifacts,
                '本次模块报告来自旧运行且已回放证据，但未被本角色独立审查。选择可能是tentative：pass只表示有条件建议与参考分析可交人审，不能把依赖视为已证明。检查缩小范围是否真实避开声明排除的依赖、依赖图是否遗漏；不能因旧报告存在就默认依赖核对confirmed。若不能支持选择范围则needs_revision或insufficient。')
            if result['status']!='task_completed': return stop(ident+'_'+result['status'])
            reviews.append(result['report']);save('reviews/'+ident,result['report'],'独立续接审查')
        if snapshot(root)!=inventory:return stop('input_changed','input_changed')
        report={'selection':selection,'screening':screening,'comparisons':comparisons,'reviews':reviews,'user_approved':False,
                'source_run':str(prior),'reused_module_ids':[m['id'] for m in selected]}
        save('RESULTS',report,'续接结果：选择、比较与审查')
        if any(r['verdict']!='pass' for r in reviews):return stop('independent_review_needs_revision','needs_revision')
        return stop('continuation_complete_user_approval_required','pending_user_review')
    except KeyboardInterrupt:return stop('user_interrupt','interrupted')
    except Exception as exc:
        state['diagnostic']=type(exc).__name__+': '+str(exc);return stop('continuation_failure','failed')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',default='input');parser.add_argument('--prior',required=True);parser.add_argument('--output',required=True);parser.add_argument('--graph-checkpoint');parser.add_argument('--downstream-from');parser.add_argument('--comparisons-from');parser.add_argument('--review-resume-from')
    args=parser.parse_args()
    result=run(args.input,args.prior,args.output,model_factory(ModelConfig(model='gpt-6.1-sol',reasoning_effort='high')),
               Budgets(calls=80,seconds=2400,context_chars=300000,reserve_calls=3,reserve_chars=35000,reserve_seconds=300,call_timeout_seconds=600),graph_checkpoint=args.graph_checkpoint,downstream_from=args.downstream_from,comparisons_from=args.comparisons_from,review_resume_from=args.review_resume_from)
    print(json.dumps(result,ensure_ascii=False,indent=2))
    return 0 if result['status']=='pending_user_review' else 1
if __name__=='__main__':raise SystemExit(main())
