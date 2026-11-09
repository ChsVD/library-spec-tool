"""Stage 1 CLI: dependency planning, target selection, screening, scoped comparison and review."""
from stage1.model_factory import ModelConfig, create_model, model_factory
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import partial
import json
from pathlib import Path
import os

from .codex_backend import BackendError
from .contracts import (validate_plan, validate_module, validate_aggregate,
                        validate_comparison, validate_review)
from .report import SECTIONS, render
from .runner import APIModel, snapshot
from .task import Budgets, run_task, write_json, write_text


ROLE_INSTRUCTIONS = {
    'planner': '你是主模型的规划会话。先分别粗读三库主要区域、公开入口和数据，按功能划分模块，给模块worker分配阅读入口与问题。覆盖所有主要区域并明确未读部分。不要自己详细理解全部模块，不比较推荐，不照搬参考库结构。模块数必须在调度上限内；可合理合并相关任务但不能隐去区域。',
    'module': '你是独立模块理解子agent。只负责分配的模块，必要时可定向读取input中的依赖。完成七项详细说明，写清大小/容量/范围及未确认项，区分材料与解释。不要跨库推荐，不替其他worker写答案，不把任务描述当证据。应尽量达到detailed，不能靠填满栏目假称理解。',
    'aggregate': '你是主模型的汇总会话。必须读取plan及全部本轮模块artifact，将原规划中的覆盖和未读范围一并核对，统一模块边界，明确遗漏、重复、冲突与未知。可定向补读原文核对，但不要替模块worker写完整说明。需返工时给具体module_id及问题；缺失新模块或未解决阻断时readiness=incomplete。禁止写跨库比较与推荐，那是专门角色的工作。',
    'comparison': '你是专门的跨库比较与推荐子agent。读取aggregate和所有模块artifact，再定向独立读取双边原文证据。按功能、表示、前提、边界与依赖比较候选，给出首选和最多两个有根据备选，或明确unable。不能主张已可直接迁移。引用模块id和比较id，首选必须有详细模块说明。不得修改模块说明来迎合推荐。',
    'review': '你是独立审查agent，不继承生成角色会话。读取aggregate、comparison与全部模块artifact，独立抽查三库原文及首选的关键证据。若拟给pass，必须用read独立读取comparison每条记录引用的全部原始行号区间，并在审查evidence中引用至少一个与首选模块证据实际重合的区间；同文件无关行不能替代。检查覆盖遗漏、模块归属、领域知识、大小条件、依赖、比较差异和推荐范围。发现须给原始证据；不能因结构检查通过就通过。pass只表示可提交用户，needs_revision或insufficient明确问题，不自动批准模块。',
}


def role_prompt(role, assignment=None):
    base = Path(__file__).resolve().parent.parent
    common = (base / 'TASK_STAGE1_MULTI.md').read_text(encoding='utf-8')
    contracts = json.loads((base / 'templates/multi-contracts.json').read_text(encoding='utf-8'))
    return (common + '\n\n' + ROLE_INSTRUCTIONS[role] + '\n\n本角色输出契约：\n' +
            json.dumps(contracts[role], ensure_ascii=False, indent=2) + '\n\n本轮任务：\n' +
            json.dumps(assignment or {}, ensure_ascii=False, indent=2))


def module_markdown(report, path):
    lines = [f"# {report['title']}", '', f"库：{report['library']}；深度：{report['depth']}", '']
    for section in SECTIONS:
        lines += ['## ' + section, '', report['sections'][section], '']
    if 'dependency_check' in report:
        check = report['dependency_check']
        lines += ['## 依赖复核', '', check['status'] + '：' + check['notes'], '']
    lines += ['## 原始证据', ''] + [f"- `{e['path']}:{e['start']}-{e['end']}`" for e in report['evidence']]
    write_text(path, '\n'.join(lines) + '\n')


def stage_markdown(role, report, path):
    """Readable intermediate records survive even when a downstream role rejects."""
    titles = {'aggregate': '主模型汇总与缺口', 'comparison': '专门比较与推荐',
              'review': '独立审查'}
    lines = ['# ' + titles[role], '', '本轮派生分析，尚未获得用户批准。原始证据仍以输入文件为准。', '']

    def evidence(items):
        return [f"- `{e['path']}:{e['start']}-{e['end']}`" for e in items]

    if role == 'aggregate':
        lines += [f"汇总状态：{report['readiness']}", '', '涉及模块：' + '、'.join(report['module_ids']), '']
        for library, coverage in report['coverage'].items():
            lines += ['## ' + library, '', '**区域与归属：** ' + coverage['mapped_areas'], '',
                      '**未读部分：** ' + coverage['unread_areas'], '', '**配置未知：** ' + coverage['configuration_unknowns'], '']
        lines += ['## 遗漏、重复、冲突与未知', '']
        for gap in report['gaps']:
            lines += [f"- [{gap['kind']}] {'阻断' if gap['blocking'] else '非阻断'}；模块：{', '.join(gap['module_ids']) or '整体'}。{gap['description']}"]
        if not report['gaps']:
            lines += ['本轮未报告缺口；这不代表穷尽全部源码。']
        lines += ['', '## 定向返工请求', '']
        lines += [f"- {x['module_id']}：{x['reason']}" for x in report['rework']] or ['无。']
        lines += ['', '## 本角色独立读取的补充证据', ''] + evidence(report['evidence'])
    elif role == 'comparison':
        for item in report['comparisons']:
            lines += ['## ' + item['id'], '',
                f"[{item['target']}](modules/{item['target']}.md) ↔ [{item['reference']}](modules/{item['reference']}.md)", '',
                f"对应状态：{item['relation']}", '', '**依据：** ' + item['basis'], '',
                '**差异：** ' + item['differences'], '', '**未知：** ' + item['unknowns'], ''] + evidence(item['evidence']) + ['']
        rec = report['recommendation']
        lines += ['## 推荐结论（待审查与用户审核）', '',
                  f"状态：{rec['confidence']}；首选：{rec.get('primary') or '无'}；备选：{', '.join(rec.get('alternatives', [])) or '无'}", '']
        for field, title in [('rationale', '理由'), ('scope', '拟处理范围'), ('dependencies', '范围外依赖'),
                             ('reference_entries', '参考入口'), ('blockers', '阻碍与未知')]:
            lines += ['**' + title + '：** ' + rec[field], '']
    else:
        lines += [f"审查结论：{report['verdict']}", '', '已审查模块：' + '、'.join(report['coverage_checked']), '', '## 审查发现', '']
        for finding in report['findings']:
            lines += [f"### {finding['id']}（{finding['severity']}）", '', finding['description'], '',
                      '涉及模块：' + '、'.join(finding['module_ids']), ''] + evidence(finding['evidence']) + ['']
        if not report['findings']:
            lines += ['本轮未报告问题；仍需用户审核。', '']
        lines += ['## 独立抽查证据', ''] + evidence(report['evidence'])
    write_text(path, '\n'.join(lines) + '\n')


def run_legacy_pipeline(root, output, model_factory, *, budgets=None, concurrency=2,
                 max_modules=24, max_rework_rounds=1, label='fixture'):
    budgets = budgets or Budgets()
    if concurrency < 1 or max_modules < 3 or max_rework_rounds < 0:
        raise ValueError('concurrency>=1, max_modules>=3, max_rework_rounds>=0 required')
    root, output = Path(root).resolve(strict=True), Path(output).resolve()
    if output.is_relative_to(root):
        raise ValueError('Pipeline output must be outside input')
    output.mkdir(parents=True, exist_ok=False)
    state = {'status': 'running', 'mode': label, 'stage': 1, 'user_approved': False,
             'completed_modules': [], 'failed_modules': [], 'planned_modules': [],
             'concurrency': concurrency, 'max_modules': max_modules,
             'max_rework_rounds': max_rework_rounds, 'tasks': {}}

    def persist():
        write_json(output / 'status.json', state)

    def task(role, ident, validator, assignment=None, artifacts=None):
        destination = output / 'tasks' / ident
        try:
            result = run_task(root, destination, model_factory(role, ident),
                role_prompt(role, assignment), validator, role=role, task_id=ident,
                budgets=budgets, artifacts=artifacts, label=label)
        except Exception as exc:
            destination.mkdir(parents=True, exist_ok=True)
            result = {'status': 'failed', 'reason': 'task_initialization_failure',
                      'diagnostic': str(exc) if isinstance(exc, BackendError) else type(exc).__name__,
                      'role': role, 'task_id': ident, 'user_approved': False}
            write_json(destination / 'status.json', result)
        return result

    def register(ident, result):
        state['tasks'][ident] = {key: result.get(key) for key in ('status', 'reason', 'calls', 'elapsed_seconds')}
        persist()

    def stop(reason, status='incomplete'):
        state.update(status=status, reason=reason)
        persist()
        return state

    persist()
    inventory = snapshot(root)
    write_json(output / 'input_snapshot.json', inventory)
    try:
        planning = task('planner', 'planner', partial(validate_plan, max_modules=max_modules),
                        {'max_modules': max_modules, 'user_priority': '未指定具体模块，由工具整体推断后用户审核'})
        register('planner', planning)
        if planning['status'] != 'task_completed':
            return stop('planner_' + planning['status'])
        plan = planning['report']
        write_json(output / 'plan.json', plan)
        state['planned_modules'] = [m['id'] for m in plan['modules']]
        persist()
        modules = {}
        assignments = {m['id']: m for m in plan['modules']}
        (output / 'modules').mkdir()

        def workers(selected, round_number, reasons=None):
            # Every planned task is scheduled; the cap is validated before this point.
            with ThreadPoolExecutor(max_workers=concurrency) as pool:
                futures = {}
                for ident in selected:
                    item = dict(assignments[ident])
                    if reasons and ident in reasons:
                        item['revision_request'] = reasons[ident]
                    artifacts = {'plan': plan}
                    if ident in modules:
                        artifacts['previous_module:' + ident] = modules[ident]
                    task_id = f'module-{ident}-r{round_number}'
                    futures[pool.submit(task, 'module', task_id, partial(validate_module, task=item), item, artifacts)] = (ident, task_id)
                for future in as_completed(futures):
                    ident, task_id = futures[future]
                    result = future.result()
                    register(task_id, result)
                    if result['status'] == 'task_completed':
                        modules[ident] = result['report']
                        write_json(output / 'modules' / f'{ident}.json', result['report'])
                        module_markdown(result['report'], output / 'modules' / f'{ident}.md')
                        if ident not in state['completed_modules']:
                            state['completed_modules'].append(ident)
                    elif ident not in state['failed_modules']:
                        state['failed_modules'].append(ident)
                    persist()

        workers(state['planned_modules'], 0)
        if state['failed_modules']:
            return stop('module_tasks_incomplete')
        aggregate = None
        for round_number in range(max_rework_rounds + 1):
            artifacts = {'plan': plan, **{'module:' + k: v for k, v in modules.items()}}
            aggregated = task('aggregate', f'aggregate-r{round_number}',
                partial(validate_aggregate, modules=list(modules.values())),
                {'rework_round': round_number, 'remaining_rework_rounds': max_rework_rounds-round_number}, artifacts)
            register(f'aggregate-r{round_number}', aggregated)
            if aggregated['status'] != 'task_completed':
                return stop('aggregate_' + aggregated['status'])
            aggregate = aggregated['report']
            write_json(output / f'aggregate-r{round_number}.json', aggregate)
            stage_markdown('aggregate', aggregate, output / f'aggregate-r{round_number}.md')
            write_json(output / 'aggregate.json', aggregate)
            stage_markdown('aggregate', aggregate, output / 'aggregate.md')
            if aggregate['readiness'] == 'ready':
                break
            requests = {item['module_id']: item['reason'] for item in aggregate['rework']}
            if not requests:
                return stop('aggregate_unresolved_coverage_or_conflicts')
            if round_number == max_rework_rounds:
                return stop('worker_rework_limit')
            workers(list(requests), round_number + 1, requests)
            if state['failed_modules']:
                return stop('worker_rework_failed')
        write_json(output / 'aggregate.json', aggregate)
        artifacts = {'plan': plan, 'aggregate': aggregate, **{'module:' + k: v for k, v in modules.items()}}
        compared = task('comparison', 'comparison',
            partial(validate_comparison, modules=list(modules.values()), aggregate=aggregate), artifacts=artifacts)
        register('comparison', compared)
        if compared['status'] != 'task_completed':
            return stop('comparison_' + compared['status'])
        comparison = compared['report']
        write_json(output / 'comparison.json', comparison)
        stage_markdown('comparison', comparison, output / 'comparison.md')
        artifacts['comparison'] = comparison
        reviewed = task('review', 'review', partial(validate_review, modules=list(modules.values()),
                        comparison=comparison), artifacts=artifacts)
        register('review', reviewed)
        if reviewed['status'] != 'task_completed':
            return stop('review_' + reviewed['status'])
        review = reviewed['report']
        write_json(output / 'independent-review.json', review)
        stage_markdown('review', review, output / 'independent-review.md')
        if review['verdict'] != 'pass':
            return stop('independent_review_' + review['verdict'], 'needs_revision')
        if snapshot(root) != inventory:
            return stop('input_changed_during_pipeline', 'input_changed')
        report = {'coverage': aggregate['coverage'], 'modules': list(modules.values()), **comparison}
        final_dir = output / 'final'
        final_dir.mkdir()
        write_json(final_dir / 'report.json', report)
        render(report, final_dir)
        write_json(final_dir / 'independent-review.json', review)
        stage_markdown('review', review, final_dir / 'independent-review.md')
        state['planned_modules_completed'] = True
        state['status'] = 'pending_user_review' if label in ('real_codex', 'real_api') else 'fixture_pipeline_complete'
        state['reason'] = 'all_roles_completed_independent_review_passed_user_approval_required'
        persist()
        return state
    except KeyboardInterrupt:
        return stop('user_interrupt', 'interrupted')
    except Exception as exc:
        state['diagnostic'] = str(exc) if isinstance(exc, BackendError) else type(exc).__name__
        return stop('pipeline_runtime_failure', 'failed')


def run_pipeline(*args, **kwargs):
    from .focused import run_pipeline as focused_pipeline
    return focused_pipeline(*args, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', default='input')
    parser.add_argument('--output', required=True)
    parser.add_argument('--backend', choices=['codex', 'api'], default='codex')
    parser.add_argument('--model')
    parser.add_argument('--reasoning-effort', choices=['low', 'medium', 'high', 'xhigh', 'max'],
                        help='explicit Codex effort override for every role; otherwise inherit whitelist')
    parser.add_argument('--calls', type=int, default=40, help='hard model-call budget per role task')
    parser.add_argument('--seconds', type=float, default=1800, help='wall-time budget per role task')
    parser.add_argument('--call-timeout', type=float, default=600, help='timeout for one model call, also bounded by remaining task time')
    parser.add_argument('--context-chars', type=int, default=120000)
    parser.add_argument('--reserve-calls', type=int, default=2)
    parser.add_argument('--reserve-chars', type=int, default=12000)
    parser.add_argument('--reserve-seconds', type=float, default=300)
    parser.add_argument('--revisions', type=int, default=2, help='validation retries per task')
    parser.add_argument('--concurrency', type=int, default=2)
    parser.add_argument('--max-modules', type=int, default=24)
    parser.add_argument('--max-rework-rounds', type=int, default=1, help='legacy compatibility only; dependency-first workflow stops on conflicts for replanning')
    args = parser.parse_args()
    try:
        budget = Budgets(args.calls, args.seconds, args.context_chars, args.reserve_calls,
                         args.reserve_chars, args.revisions, args.reserve_seconds, args.call_timeout)
        config = ModelConfig(backend=args.backend,model=args.model,reasoning_effort=args.reasoning_effort)
        create_model(config)  # Constructor preflight; no model request.
        factory = model_factory(config)
        label = 'real_codex' if args.backend == 'codex' else 'real_api'
        status = run_pipeline(args.input, args.output, factory, budgets=budget,
            concurrency=args.concurrency, max_modules=args.max_modules,
            max_rework_rounds=args.max_rework_rounds, label=label)
    except (ValueError, OSError, BackendError) as exc:
        parser.error(str(exc))
    print(json.dumps(status, ensure_ascii=False, indent=2))
    return 0 if status['status'] == 'pending_user_review' else 1


if __name__ == '__main__':
    raise SystemExit(main())
