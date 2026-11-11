"""Stage-four opt-in source deduplication and offline, delivered-message accounting.

Accounting counts Unicode characters, not tokens, bytes or model latency. Reader
logs include attempted/withheld reads and are deliberately NOT delivery evidence.
"""
import argparse
import json
from pathlib import Path
from types import MethodType

from stage1.reader import Reader


def _ranges(numbers):
    result = []
    for number in numbers:
        if result and result[-1]['end'] + 1 == number:
            result[-1]['end'] = number
        else:
            result.append({'start': number, 'end': number})
    return result


def reader_factory(base_factory=None):
    """Wrap Reader/BundleReader only when explicitly selected by stage-four v3.

    The existing reads ledger is the sole state, so restoring conversations and
    rolling back withheld feedback also restore exactly the deduplication state.
    """
    def create(root, log):
        reader = (base_factory or Reader)(root, log)
        execute = reader.execute

        def deliver(self, action):
            if not isinstance(action, dict) or action.get('tool') != 'read':
                return execute(action)
            # All permissions, range checks, bundle verification, truncation and
            # audit logging remain owned by the original implementation. Its
            # log records an attempted read, not proof of model delivery.
            before = {name: list(ranges) for name, ranges in self.reads.items()}
            result = execute(action)
            if result.get('error') or not isinstance(result.get('lines'), list):
                return result
            prior = before.get(result.get('path'), [])
            digest = result.get('sha256')
            omitted = [item['line'] for item in result['lines']
                       if any(a <= item['line'] <= b and sha == digest for a, b, sha in prior)]
            if not omitted:
                return result
            excluded = set(omitted)
            filtered = {**result, 'lines': [item for item in result['lines'] if item['line'] not in excluded],
                        'omitted_previously_delivered': _ranges(omitted),
                        'instruction': 'Use omitted lines from the earlier delivery in this same role conversation.'}
            # Preserve the underlying attempt log and separately record exactly
            # what the filter returned. Only conversation.jsonl proves delivery.
            with self.log.open('a', encoding='utf-8') as stream:
                stream.write(json.dumps({'stage4_delivery_filter': True, 'action': action,
                                         'result': filtered}, ensure_ascii=False) + '\n')
            return filtered

        reader.execute = MethodType(deliver, reader)
        return reader
    return create


def _payloads(value):
    """Only actual Reader responses and artifact envelopes count as materials.

    Never recurse into derived content: quoted source there is still derived.
    Batch sub-results occur once here; nested read log entries are not counted.
    """
    if not isinstance(value, dict) or value.get('not_delivered'):
        return
    if value.get('kind') == 'derived_interpretation_not_original_evidence':
        yield 'derived', value
    elif value.get('sha256') and value.get('path') and isinstance(value.get('lines'), list):
        yield 'original', value
    elif isinstance(value.get('results'), list):
        for row in value['results']:
            if isinstance(row, dict):
                yield from _payloads(row.get('result'))


def summarize_run(folder):
    """Summarize saved stage1.task sessions without running any model.

    First = messages preceding the first assistant response (first request).
    Later = newly appended user material, counted once rather than on every
    retransmitted request. System/control JSON and envelope overhead are prompt
    characters. Independent-role repetition excludes within-session repeats.
    Resumed transcripts are annotated separately and not merged silently.
    """
    folder = Path(folder)
    if not folder.is_dir():
        raise ValueError('Run directory does not exist: ' + str(folder))
    sessions, global_lines = [], {}
    paths = sorted(folder.rglob('status.json'))
    for path in paths:
        task = path.parent
        if not (task / 'task.md').is_file():
            continue
        status = json.loads(path.read_text(encoding='utf-8'))
        lineage = task.resolve()
        ancestor = status
        ancestors = {lineage}
        while ancestor.get('resumed_from'):
            previous = Path(ancestor['resumed_from']).resolve()
            if previous in ancestors or not (previous / 'status.json').is_file():
                break
            ancestors.add(previous)
            prior_status = json.loads((previous / 'status.json').read_text(encoding='utf-8'))
            if prior_status.get('role') != status.get('role'):
                break
            lineage, ancestor = previous, prior_status
        history_path = task / 'conversation.jsonl'
        messages = [{'role': 'system', 'content': (task / 'task.md').read_text(encoding='utf-8')}]
        if history_path.exists():
            messages += [json.loads(line) for line in history_path.read_text(encoding='utf-8').splitlines() if line]
        row = {'task': str(task.relative_to(folder)), 'role': status.get('role'),
               'calls': status.get('calls', 0), 'assistant_responses': 0,
               'model_call_started': status.get('calls', 0) > 0,
               'status': status.get('status'),
               'resumed_from': status.get('resumed_from'),
               'first': {'original': 0, 'derived': 0, 'prompt': 0},
               'later': {'original': 0, 'derived': 0, 'prompt': 0},
               'within_role_repeat_original': 0, 'independent_role_repeat_original': 0,
               'source_deliveries': 0, 'artifact_deliveries': 0,
               'first_request_chars': 0, 'request_context_chars': 0}
        phase, seen, context, sources = 'first', set(), 0, {}
        for message in messages:
            content = message['content']
            if message['role'] == 'assistant':
                row['assistant_responses'] += 1
                row['request_context_chars'] += context
                if phase == 'first':
                    row['first_request_chars'] = context
                phase = 'later'
                context += len(content)
                continue
            context += len(content)
            row[phase]['prompt'] += len(content)
            if message['role'] != 'user':
                continue
            try:
                value = json.loads(content)
            except (ValueError, TypeError):
                continue
            for kind, payload in _payloads(value):
                if kind == 'derived':
                    chars = len(json.dumps(payload['content'], ensure_ascii=False))
                    row['artifact_deliveries'] += 1
                else:
                    chars = 0
                    row['source_deliveries'] += 1
                    source = sources.setdefault((payload['sha256'], payload['path']), {
                        'sha256': payload['sha256'], 'path': payload['path'],
                        'first': 0, 'later': 0, 'within_role_repeat': 0,
                        'independent_role_repeat': 0})
                    for line in payload['lines']:
                        length = len(line['text'])
                        chars += length
                        key = (payload['sha256'], payload['path'], line['line'])
                        source[phase] += length
                        if key in seen or lineage in global_lines.get(key, set()):
                            row['within_role_repeat_original'] += length
                            source['within_role_repeat'] += length
                        elif key in global_lines:
                            row['independent_role_repeat_original'] += length
                            source['independent_role_repeat'] += length
                        seen.add(key)
                row[phase][kind] += chars
                row[phase]['prompt'] -= chars
        for key in seen:
            global_lines.setdefault(key, set()).add(lineage)
        row['sources'] = list(sources.values())
        row['unanswered_call_attempts'] = max(0, row['calls'] - row['assistant_responses'])
        sessions.append(row)
    if not sessions:
        raise ValueError('No saved role sessions (status.json and task.md) in: ' + str(folder))
    totals = {name: sum(row[name] for row in sessions) for name in
              ('calls', 'assistant_responses', 'first_request_chars', 'request_context_chars',
               'within_role_repeat_original', 'independent_role_repeat_original',
               'source_deliveries', 'artifact_deliveries')}
    totals['sessions_without_model_call'] = sum(not row['model_call_started'] for row in sessions)
    totals['unanswered_call_attempts'] = sum(row['unanswered_call_attempts'] for row in sessions)
    for phase in ('first', 'later'):
        totals[phase] = {kind: sum(row[phase][kind] for row in sessions)
                         for kind in ('original', 'derived', 'prompt')}
    return {'schema': 1, 'unit': 'Unicode characters; not model tokens',
            'delivery_basis': 'task.md and actual conversation.jsonl; attempted/withheld read logs excluded',
            'category_basis': 'Original = decoded line text (no line separators); derived = canonical JSON content only; prompt = remaining non-assistant characters, including envelopes/escaping. First/later are staged conversation deliveries; zero-call sessions are separately marked.',
            'repeat_key': ['sha256', 'path', 'line'],
            'repeat_attribution_order': 'Lexicographic saved task path; independent totals are order invariant. This is not a claim about execution order.',
            'limitations': 'Resumed transcripts include replayed historical context; same resume lineage is counted within-role when both sessions are present. Calls are saved task counters; request-context totals count requests with saved assistant responses, excluding backend retries without responses. Independent-role repeats mean distinct role sessions, including separate instances of the same named role. No latency or token claims.',
            'sessions': sessions, 'totals': totals}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('runs', nargs='+', type=Path)
    args = parser.parse_args()
    try:
        result = {str(path): summarize_run(path) for path in args.runs}
    except (ValueError, OSError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
