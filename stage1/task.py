"""One bounded role session; original and derived materials stay distinct."""
from dataclasses import dataclass, asdict
import copy
import json
import math
import os
from pathlib import Path
import time

from .reader import Reader
from .contracts import check_evidence
from .codex_backend import BackendError, BackendTimeout, BackendProtocolError


@dataclass(frozen=True)
class Budgets:
    calls: int = 40
    seconds: float = 1800
    context_chars: int = 120000
    reserve_calls: int = 2
    reserve_chars: int = 12000
    validation_retries: int = 2
    reserve_seconds: float = 300
    call_timeout_seconds: float = 600

    def __post_init__(self):
        if not math.isfinite(self.call_timeout_seconds) or self.call_timeout_seconds <= 0:
            raise ValueError('Single model-call timeout must be finite and positive')
        if self.calls < 1 or self.seconds <= 0 or self.context_chars < 1:
            raise ValueError('Task hard budgets must be positive')
        if min(self.reserve_calls, self.reserve_chars, self.reserve_seconds, self.validation_retries) < 0:
            raise ValueError('Task reserve/retry values cannot be negative')


@dataclass(frozen=True)
class ReportPolicy:
    max_report_chars: int = 12000
    repair_chars: int = 6000
    control_chars: int = 2000
    max_part_chars: int = 4000
    append_batches: bool = False

    def __post_init__(self):
        if any(type(x) is not int or x<1 for x in (self.max_report_chars,self.repair_chars,self.control_chars,self.max_part_chars)):
            raise ValueError('Report policy limits must be positive integers')

    @property
    def reserve(self):
        return self.max_report_chars+self.repair_chars+self.control_chars


def write_text(path, text):
    """Flush a complete temporary file before atomically replacing the prior version."""
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w', encoding='utf-8') as stream:
        stream.write(text)
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def write_json(path, value):
    write_text(path, json.dumps(value, ensure_ascii=False, indent=2))


def draft_markdown(value, role, task_id, status):
    body = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2)
    return (f'# {task_id}：中间输出\n\n角色：{role}；任务状态：{status}。\n\n'
            '这是模型输出的持久化副本；不代表已通过校验、独立审查或用户批准。\n\n' + body + '\n')


def run_task(root, output, model, prompt, validator, *, role, task_id, budgets,
             artifacts=None, label='fixture', allowed_tools=None, resume_from=None, backend_retries=0, allow_report_patch=False, reader_factory=None, report_policy=None, required_inputs=None, complete_bundle_evidence=False, resume_prompt_migration=None, resume_revalidate=False):
    root, output = Path(root).resolve(strict=True), Path(output).resolve()
    if output.is_relative_to(root):
        raise ValueError('Task output must be outside input')
    output.mkdir(parents=True, exist_ok=False)
    checkpoints = output / 'checkpoints'
    checkpoints.mkdir()
    artifacts = artifacts or {}
    artifact_reads = set()
    reserve_chars=max(budgets.reserve_chars,report_policy.reserve) if report_policy else budgets.reserve_chars
    reader = (reader_factory or Reader)(root, output / 'reads.jsonl')
    started = time.monotonic()
    state = {'status': 'running', 'role': role, 'task_id': task_id, 'mode': label,
             'calls': 0, 'user_approved': False, 'budgets': asdict(budgets),
             'closing': False, 'warnings': [], 'validation_failures': 0}
    messages = [{'role': 'system', 'content': prompt + '\n\nTask budgets: ' +
                 json.dumps(asdict(budgets)) + '\nDerived artifact IDs: ' +
                 json.dumps(list(artifacts), ensure_ascii=False)}]
    draft = {'role': role, 'task_id': task_id, 'state': 'not_started',
             'interpretation': {}, 'last_action': None, 'last_feedback': None}
    last_semantic_draft = 0
    last_report = None
    report_batches = {}
    protocol_diagnostic = None
    if report_policy:
        state['report_policy']=asdict(report_policy)
        state['effective_reserve_chars']=reserve_chars
        messages[0]['content']+='\nReport policy: '+json.dumps(asdict(report_policy))+'''\nKeep the assembled report within max_report_chars (JSON, including field names). Do not repeat source or dependency descriptions; cite evidence and edge IDs. Reserve includes output, repair and control feedback separately.
Optional staged output: {"tool":"report_part","fields":{...}} saves/replaces whole top-level report fields (each action <= max_part_chars). Parts are NOT validated candidates. Send {"tool":"finish"} to validate the assembled report without repeating it. Direct finish/report and patch_report remain available. Only full assembled reports passing the original validator are accepted. No new source reads during closing. A returned report may be checked locally after context exhaustion, but no further model calls are allowed and this is NOT independent review or proof.'''


    if report_policy and report_policy.append_batches:
        messages[0]['content']+='\nPreferred output is incremental: report_part fields for scalar/object sections, then report_part append for lists. Example {"tool":"report_part","batch_id":"claims-1","append":{"claims":[...]}}. Use stable unique batch IDs; replaying identical batches does not duplicate entries, changed content with the same ID is rejected. Commit small batches before exhausting budget. Finish with {"tool":"finish"}; the program validates the whole assembled report. Never omit obligations to fit a batch; split that batch instead. Existing fields can still be replaced to correct content.'

    def persist():
        state['elapsed_seconds'] = round(time.monotonic() - started, 3)
        state['context_chars'] = sum(len(x['content']) for x in messages)
        state['artifact_reads'] = sorted(artifact_reads)
        write_json(output / 'status.json', state)
        write_json(output / 'draft.json', draft)
        write_text(output / 'draft.md', draft_markdown(draft['interpretation'], role, task_id, state['status']))

    def checkpoint(value, kind):
        # Append-only versions survive later revisions, validation failure or timeout.
        basename = checkpoints / f'turn-{state["calls"]:04d}-{kind}'
        saved = {'role': role, 'task_id': task_id, 'call': state['calls'],
                 'kind': kind, 'validation': 'not_validated', 'content': value}
        write_json(basename.with_suffix('.json'), saved)
        write_text(basename.with_suffix('.md'), draft_markdown(value, role, task_id, 'not_validated'))
        state['latest_checkpoint'] = str(basename.with_suffix('.json').relative_to(output))

    def append(role_name, content):
        message = {'role': role_name, 'content': content}
        messages.append(message)
        with (output / 'conversation.jsonl').open('a', encoding='utf-8') as stream:
            stream.write(json.dumps(message, ensure_ascii=False) + '\n')

    def budget_feedback():
        used_chars = sum(len(x['content']) for x in messages)
        used_seconds = time.monotonic() - started
        return {'used': {'calls': state['calls'], 'seconds': round(used_seconds, 3), 'context_chars': used_chars},
                'remaining': {'calls': max(0, budgets.calls-state['calls']),
                              'seconds': round(max(0, budgets.seconds-used_seconds), 3),
                              'context_chars': max(0, budgets.context_chars-used_chars)},
                'closing': state['closing']}

    saved_resume_candidate = None
    if resume_from is not None:
        previous = Path(resume_from).resolve(strict=True)
        previous_status = json.loads((previous / 'status.json').read_text())
        if previous_status.get('role') != role or previous_status.get('status') in ('running', 'task_completed'):
            raise ValueError('Only a stopped unfinished task of the same role can be resumed')
        previous_system = (previous / 'task.md').read_text()
        previous_prompt=previous_system.split('\n\nTask budgets:')[0]
        if previous_prompt != prompt:
            migration=resume_prompt_migration or {}
            old=migration.get('old_max_report_chars');new=migration.get('new_max_report_chars')
            if (set(migration)!={'old_max_report_chars','new_max_report_chars'}
                    or (old is not None and (type(old) is not int or old<=0)) or (new is not None and (type(new) is not int or new<=0))
                    or ('报告字符长度不设上限' if old is None else f'报告最多{old}字符') not in previous_prompt
                    or previous_prompt.replace('报告字符长度不设上限' if old is None else f'报告最多{old}字符','报告字符长度不设上限' if new is None else f'报告最多{new}字符') != prompt):
                raise ValueError('Resume must preserve the original role instructions except explicit report-limit migration')
            write_json(output/'prompt-migration.json',{'allowed_change':'report_character_limit',**migration,
                'old_prompt':previous_prompt,'new_prompt':prompt})
            previous_system=prompt+previous_system[len(previous_prompt):]
        prior_metadata = json.loads((previous / 'model.json').read_text())
        current_metadata = model.metadata() if hasattr(model, 'metadata') else {'backend': label}
        if any(prior_metadata.get(k) != current_metadata.get(k) for k in ('model', 'reasoning_effort')):
            raise ValueError('Resume must preserve model and effort')
        messages = [{'role': 'system', 'content': previous_system}]
        history = [json.loads(line) for line in (previous / 'conversation.jsonl').read_text().splitlines()]
        def delivered_messages(history):
            for message in history:
                yield message
                if message.get('role') == 'user':
                    try:
                        data=json.loads(message['content'])
                    except (ValueError, TypeError):
                        continue
                    if isinstance(data,dict) and isinstance(data.get('results'),list):
                        for row in data['results']:
                            if isinstance(row,dict) and isinstance(row.get('result'),dict):
                                yield {'role':'user','content':json.dumps(row['result'],ensure_ascii=False)}
        for message in delivered_messages(history):
            if message.get('role') != 'user':
                continue
            try:
                material = json.loads(message['content'])
            except (ValueError, TypeError):
                continue
            if not isinstance(material, dict):
                continue
            if material.get('kind') == 'derived_interpretation_not_original_evidence':
                ident = material.get('id')
                if ident not in artifacts or artifacts[ident] != material.get('content'):
                    raise ValueError('Previously delivered artifact changed')
                artifact_reads.add(ident)
            if 'sha256' in material and isinstance(material.get('lines'), list) and material.get('path'):
                real = reader.path(material['path']).relative_to(reader.root).as_posix()
                source_lines, digest = reader.lines(real)
                if digest != material['sha256']:
                    raise ValueError('Previously delivered original evidence changed')
                for item in material['lines']:
                    n = item['line']
                    if source_lines[n-1] != item['text']:
                        raise ValueError('Previously delivered original text changed')
                    reader.reads.setdefault(real, []).append((n, n, digest))
        for message in history:
            append(message['role'], message['content'])
        draft['interpretation'] = json.loads((previous / 'draft.json').read_text()).get('interpretation', {})
        parts_path=previous/'report-parts.json'
        if report_policy and parts_path.exists():
            saved=json.loads(parts_path.read_text())
            last_report=copy.deepcopy(saved['report']);report_batches=copy.deepcopy(saved['batches'])
            write_json(output/'report-parts.json',saved)
        if resume_revalidate and previous_status.get('latest_checkpoint'):
            candidate_path = (previous/previous_status['latest_checkpoint']).resolve(strict=True)
            if not candidate_path.is_relative_to(previous):raise ValueError('Resume checkpoint escapes task')
            candidate = json.loads(candidate_path.read_text())
            if candidate.get('kind') == 'report' and candidate.get('role') == role and candidate.get('task_id') == previous_status.get('task_id'):
                saved_resume_candidate = candidate.get('content')
                state['restored_report_checkpoint'] = str(candidate_path)
        state['resumed_from'] = str(previous)
        state['previous_calls'] = previous_status.get('calls', 0)
        append('user', json.dumps({'resume': True, 'new_task_budget': asdict(budgets),
            'instruction': 'Continue the interrupted role from the preserved conversation. Original source hashes and delivered artifacts were checked. Do not reread completed evidence merely because execution resumed. Earlier incomplete status was not approval; submit only supported results.'}))
        if resume_prompt_migration:
            append('user',json.dumps({'authorized_report_limit_migration':resume_prompt_migration,
                'previous_validation_errors':json.loads((previous/'draft.json').read_text()).get('last_feedback',{}).get('validation_errors',[]),
                'instruction':'The new system report limit explicitly replaces the previous character limit. All original structure, exact inherited conditions and independently read evidence checks remain. Repair the preserved report; do not omit obligations or paraphrase inherited conditions.'},ensure_ascii=False))
    persist()
    (output / 'task.md').write_text(messages[0]['content'], encoding='utf-8')
    metadata = model.metadata() if hasattr(model, 'metadata') else {'backend': label}
    write_json(output / 'model.json', metadata)
    try:
        if saved_resume_candidate is not None:
            errors = validator(saved_resume_candidate,reader,artifact_reads)
            if report_policy and len(json.dumps(saved_resume_candidate,ensure_ascii=False)) > report_policy.max_report_chars:
                errors = list(errors) + ["report exceeds report policy character limit"]
            write_json(output/'restored-report-validation.json',{'checkpoint':state['restored_report_checkpoint'],
                'errors':errors,'note':'Original saved model response; source hashes, role instructions, model and effort rechecked; no new model generation.'})
            write_json(output/'report-attempt-1.json',saved_resume_candidate)
            if not errors:
                write_json(output/'report.json',saved_resume_candidate)
                state.update(status='task_completed',reason='saved_model_response_validated_after_resume')
                draft['interpretation']=saved_resume_candidate
                persist()
                return {**state,'report':saved_resume_candidate}
            state['validation_failures'] += 1
            last_report=copy.deepcopy(saved_resume_candidate)
            append('user',json.dumps({'report_errors':errors,'instruction':'Repair only errors in your saved report. Existing reads remain valid. Do not repeat earlier source reading.'},ensure_ascii=False))
            persist()
        if required_inputs is not None:
            pending=copy.deepcopy(required_inputs)
            if resume_from is not None:
                def delivered(action):
                    if action.get('tool')=='artifact':return action.get('id') in artifact_reads
                    if action.get('tool')=='read':
                        return not check_evidence([{'path':action['path'],'start':action['start'],
                            'end':action['start']+action['count']-1}],reader)
                    return False
                pending=[a for a in pending if not delivered(a)]
                if saved_resume_candidate is not None and complete_bundle_evidence:
                    from .evidence_completion import plan as completion_plan
                    actions,unavailable=completion_plan(saved_resume_candidate,reader)
                    if unavailable:
                        state.update(status='needs_material',reason='resume_evidence_completion_unavailable')
                        write_json(output/'material_gap.json',{'unavailable':unavailable});persist();return state
                    # Bound actual supplemental payload as well as action/line counts.
                    size=sum(len(json.dumps({'path':a['path'],'lines':reader.lines(a['path'])[0][a['start']-1:a['start']-1+a['count']]},ensure_ascii=False)) for a in actions)
                    if size>6000:
                        state.update(status='needs_material',reason='resume_evidence_completion_budget');persist();return state
                    pending+=actions
                    write_json(output/'resume-evidence-completion.json',{'actions':actions,'unavailable':[],
                        'note':'Only missing lines planned. Evidence credit is granted only after delivery below.'})
            state['required_inputs']={'total':len(pending),'delivered':0,'complete':False}
            write_json(output/'required_inputs.json',pending)
            while pending:
                action=pending[0];before=copy.deepcopy(reader.reads)
                if action.get('tool')=='artifact':
                    ident=action.get('id')
                    feedback=({'kind':'derived_interpretation_not_original_evidence','id':ident,'content':artifacts[ident]}
                              if ident in artifacts else {'error':'required artifact absent: '+str(ident)})
                elif action.get('tool')=='read':feedback=reader.execute(action)
                else:feedback={'error':'unsupported mandatory input action'}
                payload=json.dumps(feedback,ensure_ascii=False)
                used=sum(len(m['content']) for m in messages)
                reason=None
                if feedback.get('error'):reason='required_input_unavailable'
                elif action.get('tool')=='read' and feedback.get('end',0)<action['start']+action['count']-1:
                    reason='required_source_interval_not_fully_delivered'
                elif used+len(payload)>max(0,budgets.context_chars-reserve_chars):reason='required_inputs_exceed_read_budget'
                elif time.monotonic()-started>=budgets.seconds:reason='required_inputs_time_limit'
                if reason:
                    reader.reads=before
                    state.update(status='needs_material',reason=reason)
                    missing={'reason':reason,'pending_actions':pending,'blocked_feedback':feedback,
                             'instruction':'No model calls started. Split the mandatory scope or provide missing material; do not waive evidence.'}
                    write_json(output/'material_gap.json',missing)
                    draft['last_feedback']=missing;persist();return state
                append('user',payload)
                if action['tool']=='artifact':artifact_reads.add(action['id'])
                pending.pop(0);state['required_inputs']['delivered']+=1;persist()
            state['required_inputs']['complete']=True
            append('user','{"required_inputs_delivered":true,"instruction":"The program supplied mandatory inputs above to THIS role. Use them directly; do not reread merely to gain credit. This is delivery, not semantic review or proof. Read optional sources only for additional claims."}')
            if sum(len(m['content']) for m in messages)>budgets.context_chars-reserve_chars:
                state.update(status='needs_material',reason='required_inputs_exceed_read_budget')
                write_json(output/'material_gap.json',{'reason':state['reason'],'pending_actions':[], 'instruction':'Mandatory input/control payload leaves insufficient output reserve; split scope.'})
                persist();return state
            persist()
        while True:
            elapsed = time.monotonic() - started
            size = sum(len(x['content']) for x in messages)
            if state['calls'] >= budgets.calls:
                state.update(status='budget_exhausted', reason='call_limit')
                break
            if elapsed >= budgets.seconds:
                state.update(status='budget_exhausted', reason='time_limit')
                break
            if size >= budgets.context_chars:
                state.update(status='budget_exhausted', reason='context_limit')
                break
            approaching = []
            if budgets.calls - state['calls'] <= budgets.reserve_calls:
                approaching.append('call_reserve')
            if budgets.seconds - elapsed <= budgets.reserve_seconds:
                approaching.append('time_reserve')
            if budgets.context_chars - size <= reserve_chars:
                approaching.append('context_reserve')
            if approaching and not state['closing']:
                state['closing'] = True
                state['warnings'].append({'causes': approaching, 'before_call': state['calls'] + 1})
                append('user', json.dumps({'budget_warning': approaching,
                    'budget': budget_feedback(),
                    'instruction': 'Reserved closing phase. No new reads. Submit finish/report or draft/draft with explicit missing work; never invent coverage.'}))
            # Every third response must supply a semantic draft or final report. The
            # full action+feedback draft is persisted every turn regardless of cooperation.
            draft_due = state['calls'] - last_semantic_draft >= 3
            if draft_due:
                append('user', '{"draft_required":"Include draft with your next action, or finish. State findings, gaps, and next steps."}')
            if sum(len(x['content']) for x in messages) >= budgets.context_chars:
                state.update(status='budget_exhausted', reason='context_limit_before_call')
                break
            state['calls'] += 1
            persist()
            remaining = budgets.seconds - (time.monotonic() - started)
            allowance = remaining if state['closing'] else remaining - budgets.reserve_seconds
            if allowance <= 0 < remaining and not state['closing']:
                state['closing'] = True
                state['warnings'].append({'causes': ['time_reserve'], 'before_call': state['calls']})
                append('user', json.dumps({'budget_warning': 'time_reserve', 'budget': budget_feedback(),
                    'instruction': 'No new reads; submit semantic draft or supported finish within reserved time.'}))
                allowance = remaining
            if allowance <= 0:
                state.update(status='budget_exhausted', reason='time_limit_before_call')
                break
            try:
                response = model(messages, min(budgets.call_timeout_seconds, allowance))
            except BackendTimeout as exc:
                state.setdefault('backend_timeouts', []).append({'call': state['calls'],
                    'closing': state['closing'], 'timeout_seconds': min(budgets.call_timeout_seconds, allowance)})
                draft['last_feedback'] = {'confirmed_backend_timeout': True, 'diagnostic': str(exc)}
                if time.monotonic() - started >= budgets.seconds:
                    state.update(status='budget_exhausted', reason='time_limit')
                    persist()
                    break
                if state['closing']:
                    state.update(status='failed', reason='backend_timeout_during_closing', diagnostic=str(exc))
                    persist()
                    break
                state['closing'] = True
                state['warnings'].append({'causes': ['confirmed_backend_timeout_preserving_time_reserve'],
                                          'after_call': state['calls']})
                append('user', json.dumps({'budget_warning': 'confirmed_backend_timeout_preserving_time_reserve',
                    'budget': budget_feedback(), 'instruction': 'Previous call timed out and was stopped. No new reads; use reserved time for semantic draft or supported finish. No source was read by that failed call.'}))
                persist()
                continue
            except BackendProtocolError as exc:
                response=exc.response
                protocol_diagnostic={'original_chars':exc.original_chars,'parse_error':exc.parse_error,
                                     'truncated':exc.original_chars>len(exc.response)}
            except BackendError as exc:
                retries = state.setdefault('backend_retry_events', [])
                if len(retries) >= backend_retries:
                    raise
                retries.append({'call': state['calls'], 'diagnostic': str(exc),
                                'action': 'retry same conversation; no response or source feedback accepted'})
                persist()
                continue
            if not isinstance(response, str):
                raise BackendError('Role model returned non-text content.')
            write_text(output / f'raw-response-{state["calls"]}.txt', response)
            draft['state'] = 'in_progress'
            try:
                if protocol_diagnostic:raise ValueError('backend protocol error')
                action = json.loads(response)
                if not isinstance(action, dict):raise ValueError('JSON action must be an object')
            except ValueError as exc:
                diagnostic=protocol_diagnostic or {'original_chars':len(response),'truncated':len(response)>8000,
                    'parse_error':{'message':getattr(exc,'msg',str(exc)),'line':getattr(exc,'lineno',None),
                                   'column':getattr(exc,'colno',None),'position':getattr(exc,'pos',None)}}
                protocol_diagnostic=None
                append('assistant',response)
                diagnostic['response_excerpt']=response[:8000]
                write_json(output/f'format-error-{state["calls"]}.json',diagnostic)
                state['format_failures']=state.get('format_failures',0)+1
                if state.get('citation_judgment_pending'):
                    state.update(status='needs_material',reason='citation_judgment_invalid_response');persist();break
                if (state['format_failures']>1 or diagnostic['truncated'] or
                    state['calls']>=budgets.calls or time.monotonic()-started>=budgets.seconds):
                    state.update(status='failed',reason='output_format_error');persist();break
                feedback=json.dumps({'format_error':diagnostic['parse_error'],
                    'instruction':'Repair only the failed JSON action. Preserve content and prior saved batches. Return one JSON object with tool; no Markdown or surrounding prose.'},ensure_ascii=False)
                if sum(len(m['content']) for m in messages)+len(feedback)>=budgets.context_chars:
                    state.update(status='budget_exhausted',reason='format_repair_context_limit');persist();break
                append('user',feedback)
                persist();continue
            append('assistant', response)
            if state.pop('citation_judgment_pending',False):
                audit=json.loads((output/'citation_judgment.json').read_text())
                audit['response_action']=action.get('tool')
                audit['explanation']=action.get('citation_judgment',action.get('reason'))
                audit['response_received']=True
                write_json(output/'citation_judgment.json',audit)
                if (action.get('tool') not in ('finish','patch_report') or
                    not isinstance(action.get('citation_judgment'),str) or not action['citation_judgment'].strip()):
                    state.update(status='needs_material',reason='citation_judgment_requires_material')
                    write_json(output/'material_gap.json',{'reason':state['reason'],'model_reason':action.get('reason'),
                        'instruction':'Citation judgment did not produce a repaired report. Acquire missing source separately.'})
                    persist();break
            if report_policy and action.get('tool')=='finish' and 'report' not in action:
                action={**action,'report':copy.deepcopy(last_report)}
            if report_policy and action.get('tool')=='report_part':
                if allowed_tools is not None and 'report_part' not in allowed_tools:
                    append('user','{"error":"report_part disabled for this role"}')
                    persist();continue
                if time.monotonic()-started>=budgets.seconds or sum(len(m['content']) for m in messages)>budgets.context_chars:
                    state.update(status='budget_exhausted',reason='report_part_budget_exhausted');persist();break
                from .report_parts import merge as merge_part, fingerprint as part_fingerprint
                try:
                    if action.get('append') and not report_policy.append_batches:
                        raise ValueError('append batches are disabled for this role')
                    combined,replayed=merge_part(last_report,action,report_batches)
                    if len(response)>report_policy.max_part_chars:
                        raise ValueError('batch exceeds max_part_chars; split this batch, prior batches are saved')
                    if len(json.dumps(combined,ensure_ascii=False))>report_policy.max_report_chars:
                        raise ValueError('assembled report exceeds max_report_chars; prior batches retained')
                except ValueError as exc:
                    append('user',json.dumps({'error':str(exc)},ensure_ascii=False));persist();continue
                if action.get('batch_id'):report_batches[action['batch_id']]=part_fingerprint(action)
                last_report=copy.deepcopy(combined)
                draft['interpretation']=combined
                write_json(output/'report-parts.json',{'report':combined,'batches':report_batches,'validated':False})
                checkpoint(combined,'report-parts')
                last_semantic_draft=state['calls']
            if allow_report_patch and action.get('tool') == 'patch_report':
                changes = action.get('changes')
                if (not isinstance(last_report, dict) or not isinstance(changes, dict) or not changes
                        or not set(changes) <= set(last_report)):
                    append('user', '{"error":"patch_report requires a prior finish report and nonempty changes to existing top-level fields"}')
                    persist()
                    continue
                merged = copy.deepcopy(last_report)
                merged.update(copy.deepcopy(changes))
                action = {**action, 'tool': 'finish', 'report': merged}
            if action.get('tool') == 'finish' and isinstance(action.get('report'), dict):
                last_report = copy.deepcopy(action['report'])
                if report_policy and report_policy.append_batches:
                    write_json(output/'report-parts.json',{'report':last_report,'batches':report_batches,'validated':False})
            draft['last_action'] = action
            semantic = action.get('draft')
            has_draft = (isinstance(semantic, dict) and bool(semantic)) or (isinstance(semantic, str) and bool(semantic.strip()))
            has_note = isinstance(action.get('note'), str) and bool(action['note'].strip())
            if has_draft:
                draft['interpretation'] = action['draft']
                last_semantic_draft = state['calls']
                write_json(output / f'draft-turn-{state["calls"]}.json', draft)
                checkpoint(semantic, 'draft')
            if action.get('tool') == 'checkpoint' and has_note:
                draft['interpretation'] = action['note']
                checkpoint(action['note'], 'note')
            if action.get('tool') == 'finish' and 'report' in action:
                # Keep even a late/oversized returned report, without accepting it.
                draft['interpretation'] = action['report']
                checkpoint(action['report'], 'report')
            # Hard deadlines apply even if a late response would otherwise pass.
            if time.monotonic() - started >= budgets.seconds:
                state.update(status='budget_exhausted', reason='time_limit_after_response')
                persist()
                break
            context_exhausted=sum(len(x['content']) for x in messages)>budgets.context_chars
            if context_exhausted:
                if report_policy and action.get('tool')=='finish' and isinstance(action.get('report'),dict):
                    state['local_validation_after_context_limit']=True
                else:
                    state.update(status='budget_exhausted', reason='context_limit_after_response')
                    persist()
                    break
            tool = action.get('tool')
            read_snapshot = copy.deepcopy(reader.reads)
            delivered_artifact = None
            if draft_due and tool != 'finish' and not (report_policy and tool=='report_part') and not has_draft and not (tool == 'checkpoint' and has_note):
                append('user', '{"error":"A semantic draft is required now. Include findings/gaps/next steps in draft, or submit finish; this action was not executed."}')
                persist()
                continue
            if allowed_tools is not None and tool not in allowed_tools:
                append('user', json.dumps({'error': 'Tool disabled for this role; use only allowed artifact cards and finish/draft/checkpoint'}))
                persist()
                continue
            if tool == 'finish':
                report = action.get('report')
                write_json(output / f'report-attempt-{state["validation_failures"] + 1}.json', report)
                draft['interpretation'] = report
                try:
                    errors = validator(report, reader, artifact_reads)
                    if report_policy and len(json.dumps(report,ensure_ascii=False))>report_policy.max_report_chars:
                        errors=list(errors)+['report exceeds max_report_chars; shorten prose or replace fields without removing obligations']
                except (TypeError, ValueError, KeyError, AttributeError):
                    errors = ['Malformed report structure; follow the role contract']
                if state.get('citation_judgment_attempted'):
                    audit=json.loads((output/'citation_judgment.json').read_text())
                    if audit.get('response_received'):
                        audit['validation_result']='accepted_by_role_validator' if not errors else 'rejected_by_role_validator'
                        audit['validation_errors']=errors
                        audit['semantic_approval']=False
                        write_json(output/'citation_judgment.json',audit)
                if not errors:
                    state.update(status='task_completed', reason='role_output_validated', report=report)
                    write_json(output / 'report.json', report)
                    draft['state'] = 'completed'
                    persist()
                    break
                state['validation_failures'] += 1
                feedback = {'validation_errors': errors}
                if allow_report_patch:
                    feedback['repair_hint'] = 'Use patch_report with changes to existing top-level fields to avoid repeating the entire report; all validation gates still apply.'
                with (output / 'validation.jsonl').open('a', encoding='utf-8') as stream:
                    stream.write(json.dumps(feedback, ensure_ascii=False) + '\n')
                draft['last_feedback']=feedback
                evidence_gaps=[e for e in errors if (e.startswith('read required dependency/unknown detail page:')
                    or e.startswith('writer must inspect') or e.startswith('review must inspect')
                    or e.startswith('Invalid evidence: original evidence was not read')
                    or e.startswith('Invalid evidence: not_extracted')
                    or (complete_bundle_evidence and e.startswith('Invalid evidence: line exceeds file')))]
                if required_inputs is not None and evidence_gaps and complete_bundle_evidence and not state.get('evidence_completion_attempted') and not context_exhausted:
                    from .evidence_completion import plan as completion_plan
                    actions,unavailable=completion_plan(report,reader)
                    state['evidence_completion_attempted']=True
                    audit={'actions':actions,'unavailable':unavailable,'delivered':False}
                    before=copy.deepcopy(reader.reads);payloads=[]
                    if actions and not unavailable and (allowed_tools is None or 'read' in allowed_tools) and state['calls']<budgets.calls and time.monotonic()-started<budgets.seconds:
                        for item in actions:
                            response=reader.execute(item)
                            if response.get('error') or response.get('end',0)<item['start']+item['count']-1:
                                audit['reason']='source_unavailable';break
                            payloads.append(json.dumps(response,ensure_ascii=False))
                        control=json.dumps({'evidence_completion':'Additional original source supplied. Recheck the saved candidate against these conditions, then finish or patch_report. Delivery is not semantic approval.'})
                        size=sum(len(x) for x in payloads)+len(control)
                        if len(payloads)==len(actions) and size<=6000 and sum(len(m['content']) for m in messages)+size<=budgets.context_chars-(report_policy.max_report_chars+report_policy.control_chars if report_policy else reserve_chars) and time.monotonic()-started<budgets.seconds:
                            for payload in payloads:append('user',payload)
                            append('user',control);last_report=copy.deepcopy(report)
                            audit['delivered']=True
                        else:audit.setdefault('reason','completion_budget_insufficient')
                    if not audit['delivered']:reader.reads=before
                    write_json(output/'evidence_completion.json',audit)
                    if audit['delivered']:
                        persist();continue
                if required_inputs is not None and evidence_gaps and complete_bundle_evidence and not state.get('citation_judgment_attempted'):
                    from .evidence_completion import citation_feedback
                    judgment=citation_feedback(report,reader)
                    if judgment:
                        state['citation_judgment_attempted']=True
                        payload=json.dumps(judgment,ensure_ascii=False)
                        reserve=report_policy.max_report_chars+report_policy.control_chars if report_policy else reserve_chars
                        available=(not context_exhausted and state['calls']<budgets.calls
                            and time.monotonic()-started<budgets.seconds
                            and sum(len(m['content']) for m in messages)+len(payload)<=budgets.context_chars-reserve)
                        write_json(output/'citation_judgment.json',{'feedback':judgment,'delivered':available,
                            'reason':'bounded_model_judgment' if available else 'repair_budget_insufficient'})
                        if available:
                            append('user',payload);state['citation_judgment_pending']=True
                            persist();continue
                if required_inputs is not None and evidence_gaps:
                    state.update(status='needs_material',reason='report_requires_unread_evidence')
                    write_json(output/'material_gap.json',{'reason':state['reason'],'validation_errors':evidence_gaps,
                        'instruction':'Preserved report is not validated. Supply the referenced evidence in a separate bounded task; no prose-only retry.'})
                    persist();break
                if context_exhausted:
                    state.update(status='budget_exhausted',reason='context_limit_report_invalid')
                    persist();break
                if state['validation_failures'] > budgets.validation_retries:
                    state.update(status='validation_failed', reason='validation_retry_limit')
                    persist()
                    break
            elif report_policy and tool=='report_part':
                feedback={'saved_report_fields':list(action.get('fields',{}))+list(action.get('append',{})),'assembled_chars':len(json.dumps(last_report,ensure_ascii=False)),'validation':'pending_full_finish'}
            elif tool in ('draft', 'checkpoint'):
                if tool == 'checkpoint' and has_note:
                    draft['interpretation'] = action['note']
                    last_semantic_draft = state['calls']
                feedback = {'saved': True, 'closing': state['closing']}
            elif required_inputs is not None and tool=='artifact' and action.get('id') in artifact_reads:
                feedback={'already_delivered':action['id'],'instruction':'Use the previously delivered content in this conversation.'}
            elif (required_inputs is not None and tool=='read' and type(action.get('start')) is int
                  and type(action.get('count')) is int and action['count']>0
                  and not check_evidence([{'path':action.get('path'),'start':action['start'],
                                           'end':action['start']+action['count']-1}],reader)):
                feedback={'already_delivered_source':action,'instruction':'Use the exact source already supplied above; no additional read needed.'}
            elif state['closing']:
                if required_inputs is not None and (tool in ('read','artifact','search','list','batch') or tool in getattr(reader, 'extra_material_tools', ())):
                    state.update(status='needs_material',reason='new_material_requested_during_closing')
                    write_json(output/'material_gap.json',{'reason':state['reason'],'pending_actions':[action],
                        'instruction':'New evidence cannot be supplied inside output reserve. Preserve draft and start a bounded evidence task; do not retry prose.'})
                    persist();break
                feedback = {'error': 'Reading reserve exhausted; submit current report or explicit incomplete draft. New reads are disabled.'}
            elif tool == 'artifact':
                ident = action.get('id')
                if not isinstance(ident, str) or ident not in artifacts:
                    feedback = {'error': 'Unknown derived artifact ID; no filesystem artifact browsing allowed'}
                elif required_inputs is not None and ident in artifact_reads:
                    feedback = {'already_delivered':ident,'instruction':'Use the previously delivered content in this conversation.'}
                else:
                    feedback = {'kind': 'derived_interpretation_not_original_evidence',
                                'id': ident, 'content': artifacts[ident]}
                    delivered_artifact = ident
            elif (tool == 'batch' and allowed_tools is not None and isinstance(action.get('actions'),list)
                  and any(not isinstance(a,dict) or a.get('tool') not in allowed_tools
                          for a in action['actions'])):
                feedback = {'error':'Batch contains a tool disabled for this role'}
            else:
                feedback = reader.execute(action)
            feedback['budget'] = budget_feedback()
            payload = json.dumps(feedback, ensure_ascii=False)
            used = sum(len(x['content']) for x in messages)
            material = (tool in ('read', 'search', 'list', 'artifact', 'batch') or tool in getattr(reader, 'extra_material_tools', ())) and not state['closing']
            normal_limit = max(0, budgets.context_chars - reserve_chars)
            if material and used + len(payload) > normal_limit:
                # Retain the entire result for audit, but do not claim the model read it.
                write_json(output / f'withheld-feedback-{state["calls"]}.json', feedback)
                reader.reads = read_snapshot
                delivered_artifact = None
                state['closing'] = True
                state['warnings'].append({'causes': ['feedback_would_consume_context_reserve'],
                                          'after_call': state['calls']})
                feedback = {'not_delivered': True, 'reason': 'feedback_would_consume_context_reserve',
                    'instruction': 'Complete material saved for audit but NOT supplied to you and NOT citable. No further reads. Use reserve to submit a draft or supported report with gaps.',
                    'budget': budget_feedback()}
                payload = json.dumps(feedback, ensure_ascii=False)
            if used + len(payload) > budgets.context_chars:
                reader.reads = read_snapshot
                state.update(status='budget_exhausted', reason='context_limit_cannot_deliver_control_feedback')
                persist()
                break
            if delivered_artifact:
                artifact_reads.add(delivered_artifact)
            draft['last_feedback'] = feedback
            append('user', payload)
            persist()
    except KeyboardInterrupt:
        state.update(status='interrupted', reason='user_interrupt')
    except Exception as exc:
        state.update(status='failed', reason='model_or_runtime_failure',
                     diagnostic=str(exc) if isinstance(exc, BackendError) else type(exc).__name__)
        if isinstance(exc, BackendError) and exc.details is not None:
            state['backend_failure_details'] = exc.details
    finally:
        persist()
    return state
