"""Dependency-first stage 1. Deep reads are scoped after responsibility screening."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
import json
from pathlib import Path
from .task import Budgets, run_task, write_json, write_text
from .runner import snapshot
from .contracts import validate_module, nonempty
from .focused_contracts import (validate_graph_plan, dependency_frontier, validate_selection,
                                validate_screening, validate_pair, validate_focused_review)
from .codex_backend import BackendError

BASE = Path(__file__).resolve().parent.parent
INSTRUCTIONS = {
 'planner': '分别划分三库全部主要区域，输出轻量模块卡片和初步依赖图。职责与边界应足以筛选对应模块。A.dependencies中的prerequisite=B表示证明A需要先处理B，不能反向。区分call/representation/specification/build，证据不足标unknown；外部依赖用prerequisite=null及external名称。跨库相似不是依赖。dependency_status=checked仅表示已在规划深度核对依赖，不表示证明完成；没有依赖也须说明核对范围和证据，不能从没有搜索到调用推出无依赖。不要深读全部实现或比较参考适用性。循环如实保留；不要为制造叶节点删边。',
 'selection': '先读plan与dependency_frontier，从eligible目标模块中提出一个下一步模块。依据依赖、职责、范围可控性和影响解释选择，不按是否有参考库反向挑选。独立读取所选模块卡片的全部原文引用以核对边界。eligible只是图上的未阻断候选，不保证可证。无合适候选输出unable，不把unknown依赖当已解决，也不能越过循环。scope明确整个模块或职责完整的函数组及其源文件边界，供阶段2枚举组内全部函数；不得因单个函数更容易而默默缩成单函数试验。未处理函数保留为待处理，批次大小不是选择范围。最终需用户审核。',
 'screening': '只读取所选目标和所有参考模块的card产物，按职责与边界逐项筛选。只可用artifact/draft/checkpoint/finish；不能读取源码、完整模块报告或做表示/lemma适用性判断。每个参考卡片恰好出现一次：match表示值得深入，no_match说明职责或边界不符，unknown说明卡片不足。不能跳过不确定项，不能把match当可复用。目标不可更换。',
 'module': '只深入分配的目标或初筛match参考模块，必要时定向读取依赖原文，形成七项说明。区分材料、解释和未知，明确长度/容量/范围、前提、表示和证明状态。dependency_check.status使用confirmed/conflict/unknown，并用notes说明深读是否支持卡片依赖与范围；发现新先决条件不得隐去。不能选择新目标、生成新规约/lemma/strategy或证明。',
 'comparison': '只比较指定目标与已通过职责初筛的一个参考模块。先读selection、screening和两份module产物，再独立核对双边原文。说明表示、前提、大小容量、依赖、已有证明状态、适配方式与未知。id必须使用任务给定comparison_id；relation=candidate/none/unknown。可以推翻初筛，不因原内容有证明就声称修改仍成立。不换目标，不生成证明或strategy。',
 'review': '独立审查本轮选择与定向比较，不宣称全库详读。读取plan、dependency_frontier、selection、screening及本轮所有module和comparison产物。检查边方向、遗漏和循环、选择依据、初筛是否误排或证据不足、目标深读是否发现新依赖，以及表示/前提差异。拟pass时独立读取目标卡片、选择证据、目标依赖证据以及所有比较引用的全部原文区间；审查evidence须与目标模块证据区间相交。coverage_checked只列本轮深读模块，findings说明未知的影响。缺少匹配本身不否定依赖优先选择，但不得编造参考。pass只表示可交用户审核。'
}


def prompt(role, assignment):
    common = (BASE/'TASK_STAGE1_MULTI.md').read_text(encoding='utf-8')
    contracts = json.loads((BASE/'templates/focused-contracts.json').read_text(encoding='utf-8'))
    return common + '\n\n' + INSTRUCTIONS[role] + '\n输出契约：\n' + json.dumps(contracts[role], ensure_ascii=False) + '\n任务：\n' + json.dumps(assignment, ensure_ascii=False)


def card(module):
    return {k: module[k] for k in ('id', 'library', 'title', 'responsibilities', 'boundary')}


def readable(path, title, report):
    lines = ['# ' + title, '', '派生分析，待用户审核；保存或结构检查通过不等于结论已证明。', '']
    def walk(value, depth=0):
        if isinstance(value, dict):
            for key, val in value.items():
                if isinstance(val, (dict, list)):
                    lines.append('  '*depth + '- **' + key + '**：'); walk(val, depth+1)
                else: lines.append('  '*depth + '- **' + key + '**：' + str(val))
        elif isinstance(value, list):
            if not value: lines.append('  '*depth + '- 无')
            for item in value:
                if isinstance(item, dict):
                    lines.append('  '*depth + '- 记录'); walk(item, depth+1)
                else: lines.append('  '*depth + '- ' + str(item))
    walk(report)
    write_text(path, '\n'.join(lines)+'\n')


def graph_markdown(plan, frontier, path):
    lines = ['# 模块依赖图', '', '箭头 A → B 表示 A 依赖 B。虚线为构建关系或未确认关系；外部依赖和未知在下方列出。图不表示证明已完成。', '', '```mermaid', 'graph TD']
    names = {m['id']: 'n'+str(i) for i,m in enumerate(plan['modules'])}
    for ident,node in names.items(): lines.append(f'  {node}["{ident}"]')
    for m in plan['modules']:
        for e in m['dependencies']:
            if e['prerequisite']:
                arrow = '-->' if e['certainty']=='confirmed' and e['kind']!='build' else '-.->'
                lines.append(f"  {names[m['id']]} {arrow} {names[e['prerequisite']]}")
    lines += ['```', '', '## 图上的候选（仍需核对）', '', ', '.join(frontier['eligible']) or '无', '', '## 循环依赖', '', str(frontier['cycles']), '', '## 逐模块依赖与边界', '']
    for m in plan['modules']:
        lines += ['### '+m['id'], '', m['responsibilities'], '', m['boundary'], '', m['dependency_notes'], '']
        for e in m['dependencies']:
            lines.append(f"- {e['prerequisite'] or e['external']}；{e['kind']}；{e['certainty']}：{e['reason']}")
        for e in m['evidence']: lines.append(f"- 规划证据：`{e['path']}:{e['start']}-{e['end']}`")
        lines.append('')
    write_text(path,'\n'.join(lines)+'\n')


def validate_deep(report, reader, reads, *, task):
    errors = validate_module(report, reader, reads, task=task)
    if not isinstance(report, dict): return errors
    check = report.get('dependency_check')
    if not isinstance(check, dict) or check.get('status') not in ('confirmed','conflict','unknown') or not nonempty(check.get('notes')):
        errors.append('dependency_check requires confirmed/conflict/unknown status and notes')
    return errors


def run_pipeline(root, output, model_factory, *, budgets=None, concurrency=2, max_modules=24,
                 max_rework_rounds=1, label='fixture'):
    from .multi import module_markdown
    budgets = budgets or Budgets()
    if concurrency < 1 or max_modules < 3 or max_rework_rounds < 0: raise ValueError('invalid pipeline limits')
    root, output = Path(root).resolve(strict=True), Path(output).resolve()
    if output.is_relative_to(root): raise ValueError('Pipeline output must be outside input')
    output.mkdir(parents=True, exist_ok=False)
    state = {'status':'running', 'workflow':'dependency_first_v1', 'stage':1, 'mode':label,
             'user_approved':False, 'tasks':{}, 'completed_modules':[], 'failed_modules':[],
             'planned_modules':[], 'deep_read_modules':[], 'selected_module':None,
             'rework_policy':'stop_with_artifacts_on_dependency_conflict; legacy max_rework_rounds is not used'}
    inventory = snapshot(root)
    write_json(output/'input_snapshot.json',inventory)
    def persist(): write_json(output/'status.json', state)
    def stop(reason, status='incomplete'):
        state.update(status=status,reason=reason); persist(); return state
    def save(name, report, title):
        write_json(output/(name+'.json'),report); readable(output/(name+'.md'),title,report)
    def task(role, ident, validator, assignment, artifacts=None, restricted=False):
        result = run_task(root, output/'tasks'/ident, model_factory(role, ident), prompt(role,assignment),
                          validator, role=role, task_id=ident, budgets=budgets, artifacts=artifacts, label=label,
                          allowed_tools={'artifact','draft','checkpoint','finish'} if restricted else None)
        return result
    def register(ident,result):
        state['tasks'][ident]={k:result.get(k) for k in ('status','reason','calls','elapsed_seconds')}; persist()
    def execute(role, ident, validator, assignment, artifacts=None, restricted=False):
        result=task(role,ident,validator,assignment,artifacts,restricted); register(ident,result); return result
    persist()
    try:
        result=execute('planner','planner',partial(validate_graph_plan,max_modules=max_modules),{'max_modules':max_modules})
        if result['status']!='task_completed': return stop('planner_'+result['status'])
        plan=result['report']; save('plan',plan,'全库模块卡片与依赖规划')
        state['planned_modules']=[m['id'] for m in plan['modules']]
        frontier=dependency_frontier(plan); save('dependency_frontier',frontier,'依赖候选与阻断')
        write_json(output/'dependency_graph.json', {'nodes': [m['id'] for m in plan['modules']],
            'edges': [{'dependent': m['id'], **e} for m in plan['modules'] for e in m['dependencies']],
            'frontier': frontier})
        graph_markdown(plan,frontier,output/'dependency_graph.md')
        artifacts={'plan':plan,'dependency_frontier':frontier}
        result=execute('selection','selection',partial(validate_selection,plan=plan,frontier=frontier),{},artifacts)
        if result['status']!='task_completed': return stop('selection_'+result['status'])
        selection=result['report']; save('selection',selection,'依赖优先选择（待审核）')
        if selection['status']=='unable': return stop('no_supported_target','needs_revision')
        state['selected_module']=selection['primary']; persist()
        target=next(m for m in plan['modules'] if m['id']==selection['primary'])
        references=[m for m in plan['modules'] if m['library']!='openssl']
        result=execute('screening','screening',partial(validate_screening,target=target,references=references),
                       {'target':target['id']},{'card:'+m['id']:card(m) for m in [target]+references},True)
        if result['status']!='task_completed': return stop('screening_'+result['status'])
        screening=result['report']; save('screening',screening,'职责与边界初筛')
        matched={c['reference'] for c in screening['candidates'] if c['decision']=='match'}
        selected=[target]+[m for m in references if m['id'] in matched]
        state['deep_read_modules']=[m['id'] for m in selected]; persist()
        modules={}; (output/'modules').mkdir()
        with ThreadPoolExecutor(max_workers=concurrency) as pool:
            jobs={pool.submit(task,'module','module-'+m['id'],partial(validate_deep,task=m),m):m for m in selected}
            for future in as_completed(jobs):
                m=jobs[future]
                try: result=future.result()
                except Exception as exc:
                    result={'status':'failed','reason':'task_initialization_failure','diagnostic':type(exc).__name__}
                register('module-'+m['id'],result)
                if result['status']=='task_completed':
                    modules[m['id']]=result['report']; state['completed_modules'].append(m['id'])
                    write_json(output/'modules'/(m['id']+'.json'),result['report'])
                    module_markdown(result['report'],output/'modules'/(m['id']+'.md'))
                else: state['failed_modules'].append(m['id'])
                persist()
        if state['failed_modules']: return stop('module_tasks_incomplete')
        if modules[target['id']]['dependency_check']['status']!='confirmed':
            return stop('target_dependencies_need_replanning','needs_revision')
        comparisons=[]
        (output/'comparisons').mkdir()
        # Each pair has its own context; never send every detailed report to a comparator.
        for reference in selected[1:]:
            pair_artifacts={'selection':selection,'screening':{'target':target['id'],'candidates':[c for c in screening['candidates'] if c['reference']==reference['id']]},
                            'module:'+target['id']:modules[target['id']], 'module:'+reference['id']:modules[reference['id']]}
            ident='comparison-'+reference['id']
            result=execute('comparison',ident,partial(validate_pair,target=target,reference=reference),
                           {'target':target['id'],'reference':reference['id'],'comparison_id':'pair-'+reference['id']},pair_artifacts)
            if result['status']!='task_completed': return stop(ident+'_'+result['status'])
            report=result['report']
            if any(c['id']==report['id'] for c in comparisons): return stop('duplicate_comparison_id')
            comparisons.append(report); save('comparisons/'+reference['id'],report,'定向深入比较')
        # Review in bounded pairs too. A matchless run still reviews the selected target.
        reviews=[]; (output/'reviews').mkdir()
        for reference in selected[1:] or [None]:
            scope=[modules[target['id']]]+([modules[reference['id']]] if reference else [])
            pairs=[c for c in comparisons if reference and c['reference']==reference['id']]
            review_artifacts={**artifacts,'selection':selection,'screening':screening,
                              **{'module:'+m['id']:m for m in scope}, **{'comparison:'+c['id']:c for c in pairs}}
            ident='review-'+(reference['id'] if reference else target['id'])
            result=execute('review',ident,partial(validate_focused_review,plan=plan,selection=selection,
                           screening=screening,modules=scope,comparisons=pairs),
                           {'coverage_checked':[m['id'] for m in scope]},review_artifacts)
            if result['status']!='task_completed': return stop(ident+'_'+result['status'])
            review=result['report']; reviews.append(review); save('reviews/'+ident,review,'独立定向审查')
        if any(r['verdict']!='pass' for r in reviews): return stop('independent_review_needs_revision','needs_revision')
        if snapshot(root)!=inventory: return stop('input_changed_during_pipeline','input_changed')
        # No match does not undo dependency order. Report it without inventing a reference.
        report={'selection':selection,'screening':screening,'comparisons':comparisons,
                'module_ids':state['deep_read_modules'],'review_scope':'selected target and matched references only',
                'unresolved_screening':[c for c in screening['candidates'] if c['decision']=='unknown'],
                'user_approved':False}
        (output/'final').mkdir(); save('final/report',report,'下一模块与参考适用性（待用户审核）')
        state['status']='pending_user_review' if label in ('real_codex','real_api') else 'fixture_pipeline_complete'
        state['reason']='dependency_selection_and_scoped_review_complete_user_approval_required'; persist(); return state
    except KeyboardInterrupt: return stop('user_interrupt','interrupted')
    except Exception as exc:
        state['diagnostic']=str(exc) if isinstance(exc,BackendError) else type(exc).__name__
        return stop('pipeline_runtime_failure','failed')
