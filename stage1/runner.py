"""Legacy single-session APIs; CLI now delegates to the multi-role stage 1 pipeline."""
from stage1.model_factory import ModelConfig, create_model, model_factory
import argparse
import hashlib
import json
import os
from pathlib import Path
import time
from urllib import error, request, parse

from .reader import Reader
from .report import render, validate
from .codex_backend import BackendError


class APIModel:
    def __init__(self, endpoint, model, key):
        parsed = parse.urlsplit(endpoint)
        if parsed.scheme != 'https' or parsed.username or parsed.password or parsed.query or parsed.fragment:
            raise ValueError('API endpoint must be HTTPS without embedded credentials, query, or fragment')
        if not model or not key:
            raise ValueError('An explicit model and API key are required')
        self.endpoint, self.model, self.key = endpoint, model, key

    def __call__(self, messages, timeout):
        body = json.dumps({'model': self.model, 'messages': messages,
                           'response_format': {'type': 'json_object'}}).encode()
        req = request.Request(self.endpoint, data=body, headers={
            'Authorization': 'Bearer ' + self.key, 'Content-Type': 'application/json'})
        # Do not forward credentials to redirected endpoints.
        class NoRedirect(request.HTTPRedirectHandler):
            def redirect_request(self, *args, **kwargs):
                return None
        try:
            with request.build_opener(NoRedirect).open(req, timeout=timeout) as response:
                raw = response.read(2_000_001)
                if len(raw) > 2_000_000:
                    raise RuntimeError('API response exceeds 2 MB')
                return json.loads(raw)['choices'][0]['message']['content']
        except error.HTTPError as exc:
            raise RuntimeError(f'Model HTTP failure ({exc.code}); response body omitted') from None
        except (error.URLError, TimeoutError):
            raise RuntimeError('Model connection or timeout failure; credentials omitted') from None


def snapshot(root):
    entries = []
    for parent, dirs, files in os.walk(root, followlinks=False):
        dirs.sort()
        for name in sorted(dirs + files):
            path = Path(parent) / name
            rel = path.relative_to(root).as_posix()
            if path.is_symlink():
                entries.append({'path': rel, 'symlink': os.readlink(path)})
            elif path.is_file():
                entries.append({'path': rel, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    return entries


def run(root, output, model, task, *, calls=100, seconds=900, context_chars=300000,
        revisions=3, label='real_api', model_name='unspecified'):
    root, output = Path(root).resolve(strict=True), Path(output).absolute()
    if output.resolve().is_relative_to(root):
        raise ValueError('Output must be outside input')
    output.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    status = {'status': 'running', 'mode': label, 'model': model_name,
              'calls': 0, 'stage': 1, 'user_approved': False,
              'budgets': {'calls': calls, 'seconds': seconds, 'context_chars': context_chars,
                          'report_revisions': revisions}}

    def save_status():
        status['elapsed_seconds'] = round(time.monotonic() - start, 2)
        (output / 'status.json').write_text(json.dumps(status, ensure_ascii=False, indent=2), encoding='utf-8')

    save_status()
    messages = [{'role': 'system', 'content': task}]
    reader = Reader(root, output / 'reads.jsonl')
    report_failures = 0
    try:
        inventory = snapshot(root)
        (output / 'input_snapshot.json').write_text(json.dumps(inventory, ensure_ascii=False, indent=2), encoding='utf-8')
        (output / 'task.md').write_text(task, encoding='utf-8')
        metadata = model.metadata() if hasattr(model, 'metadata') else {'model': model_name}
        metadata.update(mode=label, note='Credentials and API endpoints deliberately not recorded.')
        (output / 'model.json').write_text(json.dumps(metadata, indent=2), encoding='utf-8')
        for _ in range(calls):
            remaining = seconds - (time.monotonic() - start)
            if remaining <= 0 or sum(len(m['content']) for m in messages) > context_chars:
                status.update(status='budget_exhausted', reason='time or context limit; analysis incomplete')
                break
            response = model(messages, min(120, remaining))
            status['calls'] += 1
            if not isinstance(response, str):
                raise RuntimeError('Model returned non-text content')
            messages.append({'role': 'assistant', 'content': response})
            with (output / 'conversation.jsonl').open('a', encoding='utf-8') as stream:
                stream.write(json.dumps({'response': response}, ensure_ascii=False) + '\n')
            if time.monotonic() - start > seconds:
                status.update(status='budget_exhausted', reason='time limit reached; response retained')
                break
            try:
                action = json.loads(response)
                if not isinstance(action, dict):
                    raise ValueError('Action must be an object')
            except (ValueError, TypeError):
                feedback = {'error': 'Return one JSON object with tool or report'}
            else:
                if action.get('tool') == 'finish':
                    report = action.get('report')
                    (output / f'report-attempt-{report_failures + 1}.json').write_text(
                        json.dumps(report, ensure_ascii=False, indent=2), encoding='utf-8')
                    try:
                        errors = validate(report, reader)
                    except (TypeError, KeyError, AttributeError):
                        errors = ['Malformed nested report structure; follow the provided contract']
                    if not errors:
                        if snapshot(root) != inventory:
                            status.update(status='input_changed', reason='Input changed during analysis; rerun required')
                            break
                        (output / 'report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding='utf-8')
                        render(report, output)
                        status.update(status='pending_user_review' if label in ('real_api', 'real_codex') else 'fixture_complete',
                                      note='Structural checks only. No semantic acceptance or stage 2 approval.')
                        break
                    report_failures += 1
                    feedback = {'report_errors': errors, 'failed_attempt': report_failures}
                    with (output / 'validation.jsonl').open('a', encoding='utf-8') as stream:
                        stream.write(json.dumps(feedback, ensure_ascii=False) + '\n')
                    if report_failures > revisions:
                        status.update(status='validation_failed', reason='Report revision limit reached')
                        break
                elif action.get('tool') == 'checkpoint':
                    # This is analysis, not evidence; retains partial understanding on interruption.
                    note = action.get('note')
                    feedback = {'saved': isinstance(note, str)}
                    if isinstance(note, str):
                        with (output / 'checkpoints.md').open('a', encoding='utf-8') as stream:
                            stream.write(note + '\n\n')
                else:
                    feedback = reader.execute(action)
            payload = json.dumps(feedback, ensure_ascii=False)
            messages.append({'role': 'user', 'content': payload})
            with (output / 'conversation.jsonl').open('a', encoding='utf-8') as stream:
                stream.write(json.dumps({'feedback': feedback}, ensure_ascii=False) + '\n')
            save_status()
        else:
            status.update(status='budget_exhausted', reason='Model call limit reached; analysis incomplete')
    except KeyboardInterrupt:
        status.update(status='interrupted', reason='Interrupted; intermediate records retained')
    except Exception as exc:
        # Do not serialize exception strings from arbitrary provider code (could contain secrets).
        status.update(status='failed', reason=f'{type(exc).__name__}; inspect sanitized diagnostics and configuration')
        if isinstance(exc, BackendError) or (isinstance(exc, RuntimeError) and str(exc).startswith(('Model HTTP failure', 'Model connection', 'API response'))):
            status['reason'] = str(exc)
    finally:
        save_status()
    return status


def legacy_main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', default='input')
    parser.add_argument('--output', required=True)
    parser.add_argument('--backend', choices=['codex', 'api'], default='codex')
    parser.add_argument('--model', help='Optional explicit model; Codex otherwise inherits its model selection')
    parser.add_argument('--endpoint', default=os.getenv('STAGE1_API_URL'))
    parser.add_argument('--calls', type=int, default=100)
    parser.add_argument('--seconds', type=int, default=900)
    parser.add_argument('--context-chars', type=int, default=300000)
    parser.add_argument('--revisions', type=int, default=3)
    args = parser.parse_args()
    if min(args.calls, args.seconds, args.context_chars) <= 0 or args.revisions < 0:
        parser.error('Budgets must be positive; revisions must be nonnegative')
    base = Path(__file__).resolve().parent.parent
    try:
        if args.backend == 'codex':
            model = create_model(ModelConfig(model=args.model))
            model_name = model.model or 'codex_cli_default'
            label = 'real_codex'
        else:
            key = os.getenv('STAGE1_API_KEY')
            model_name = args.model or os.getenv('STAGE1_MODEL')
            if not args.endpoint or not model_name or not key:
                parser.error('API backend requires STAGE1_API_URL, STAGE1_MODEL, STAGE1_API_KEY. The default codex backend uses your existing login.')
            model = create_model(ModelConfig(backend="api",endpoint=args.endpoint,model=model_name,api_key=key))
            label = 'real_api'
    except (ValueError, BackendError) as exc:
        parser.error(str(exc))
    task = (base / 'TASK_STAGE1.md').read_text(encoding='utf-8')
    task += '\n\n' + (base / 'templates' / 'report-contract.json').read_text(encoding='utf-8')
    status = run(args.input, args.output, model, task, calls=args.calls, seconds=args.seconds,
                 context_chars=args.context_chars, revisions=args.revisions, model_name=model_name, label=label)
    print(json.dumps(status, ensure_ascii=False, indent=2))
    return 0 if status['status'] == 'pending_user_review' else 1


def main():
    from .multi import main as multi_main
    return multi_main()


if __name__ == '__main__':
    raise SystemExit(main())
