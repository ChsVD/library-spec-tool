"""Small real Codex/Reader smoke check; never analyzes or recommends a module."""
import argparse
import json
from pathlib import Path
import time

from .codex_backend import BackendError
from .model_factory import ModelConfig, create_model
from .reader import Reader


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', default='input')
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    root, output = Path(args.input).resolve(), Path(args.output).resolve()
    if output.is_relative_to(root):
        parser.error('Output must be outside input')
    output.mkdir(parents=True, exist_ok=False)
    model = create_model(ModelConfig())
    reader = Reader(root, output / 'reads.jsonl')
    messages = [{'role': 'system', 'content': (
        '进行小范围真实连通检查，不分析模块。第一条回复严格为 '
        '{"tool":"read","path":"README.md","start":1,"count":12}。'
        '收到读取内容后，仅回复 {"tool":"checkpoint","note":"..."}；'
        'note 根据读取内容简述三个库的角色，包含 openssl、sm2、mini-gmp。'
        '不要输出其他内容，也不要调用原生工具。')}]
    status = {'mode': 'real_codex_smoke', 'status': 'running', 'full_library_analysis': False,
              'user_approved': False, 'calls': 0}
    started = time.monotonic()
    try:
        for step in range(2):
            answer = model(messages, 120)
            status['calls'] += 1
            action = json.loads(answer)
            messages.append({'role': 'assistant', 'content': answer})
            if step == 0:
                if action != {'tool': 'read', 'path': 'README.md', 'start': 1, 'count': 12}:
                    raise BackendError('Smoke model did not request the specified bounded read.')
                result = reader.execute(action)
                if 'error' in result:
                    raise BackendError('Smoke README read failed; check the input path.')
                messages.append({'role': 'user', 'content': json.dumps(result, ensure_ascii=False)})
            elif action.get('tool') != 'checkpoint' or not all(
                    name in action.get('note', '').lower() for name in ('openssl', 'sm2', 'mini-gmp')):
                raise BackendError('Smoke second action did not reflect the supplied three-library input.')
            (output / 'conversation.json').write_text(json.dumps(messages, ensure_ascii=False, indent=2), encoding='utf-8')
        status['status'] = 'real_codex_smoke_completed'
    except BackendError as exc:
        status.update(status='failed', reason=str(exc))
    finally:
        status['elapsed_seconds'] = round(time.monotonic() - started, 2)
        (output / 'status.json').write_text(json.dumps(status, ensure_ascii=False, indent=2), encoding='utf-8')
        (output / 'model.json').write_text(json.dumps(model.metadata(), ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(status, ensure_ascii=False, indent=2))
    return 0 if status['status'] == 'real_codex_smoke_completed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
