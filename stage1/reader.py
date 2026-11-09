"""Read-only tools. No subprocess, script execution, or network capability."""
import copy
import hashlib
import json
import os
from pathlib import Path


class Reader:
    def __init__(self, root, log):
        self.root = Path(root).resolve(strict=True)
        self.log = Path(log)
        self.reads = {}

    def path(self, name):
        if not isinstance(name, str) or Path(name).is_absolute() or '\\' in name:
            raise ValueError('Use an input-relative POSIX path')
        if '..' in Path(name).parts:
            raise ValueError('Parent traversal is forbidden')
        path = (self.root / name).resolve(strict=True)
        if not path.is_relative_to(self.root):
            raise ValueError('Resolved path escapes input boundary')
        return path

    def lines(self, name):
        path = self.path(name)
        if not path.is_file():
            raise ValueError('Not a regular file')
        # Reject oversized/binary files explicitly rather than pretending they are empty.
        if path.stat().st_size > 8_000_000:
            raise ValueError('File exceeds 8 MB text limit; record this coverage gap')
        data = path.read_bytes()
        if b'\0' in data:
            raise ValueError('Binary file is not supported')
        return data.decode('utf-8', errors='strict').splitlines(), hashlib.sha256(data).hexdigest()

    def files(self, directory):
        base = self.path(directory)
        if base.is_file():
            yield base.relative_to(self.root).as_posix()
            return
        if not base.is_dir():
            raise ValueError('Not a directory or file')
        for parent, dirs, files in os.walk(base, followlinks=False):
            dirs[:] = sorted(d for d in dirs if not (Path(parent) / d).is_symlink())
            for name in sorted(files):
                yield (Path(parent) / name).relative_to(self.root).as_posix()

    def execute(self, action):
        try:
            op = action['tool']
            name = action.get('path', '.')
            if op == 'list':
                base = self.path(name)
                if not base.is_dir():
                    raise ValueError('Not a directory')
                offset = self.integer(action, 'offset', 0, 0, 1_000_000)
                items = []
                for p in sorted(base.iterdir()):
                    item = {'path': p.relative_to(self.root).as_posix()}
                    try:
                        target = self.path(item['path'])
                        item['kind'] = 'directory' if target.is_dir() else 'file'
                    except (ValueError, OSError):
                        item['kind'] = 'blocked_or_missing_link'
                    items.append(item)
                result = {'entries': items[offset:offset + 100], 'total': len(items),
                          'truncated': offset + 100 < len(items), 'next_offset': offset + 100}
            elif op == 'read':
                start = self.integer(action, 'start', 1, 1, 10_000_000)
                count = self.integer(action, 'count', 120, 1, 200)
                lines, digest = self.lines(name)
                if start > max(1, len(lines)):
                    raise ValueError('Start line exceeds file length')
                selected, size = [], 0
                for index in range(start - 1, min(len(lines), start - 1 + count)):
                    line = lines[index]
                    if size + len(line) > 24000:
                        break
                    selected.append({'line': index + 1, 'text': line})
                    size += len(line)
                if not selected and lines:
                    raise ValueError('Single line exceeds 24000 characters; record coverage gap')
                end = start + len(selected) - 1
                canonical = self.path(name).relative_to(self.root).as_posix()
                self.reads.setdefault(canonical, []).append((start, end, digest))
                result = {'path': canonical, 'lines': selected, 'sha256': digest,
                          'total_lines': len(lines), 'start': start, 'end': end,
                          'truncated': end < len(lines), 'next_start': end + 1}
            elif op == 'search':
                result = self.search(action)
            elif op == 'batch':
                result = self.batch(action)
            else:
                raise ValueError('Unknown tool; only list, search, read, batch are allowed')
        except (KeyError, ValueError, OSError, UnicodeError, TypeError) as exc:
            result = {'error': str(exc)}
        with self.log.open('a', encoding='utf-8') as stream:
            stream.write(json.dumps({'action': action, 'result': result}, ensure_ascii=False) + '\n')
        return result

    def search(self, action):
        name = action.get('path', '.')
        query = action.get('query')
        if not isinstance(query, str) or not 1 <= len(query) <= 200:
            raise ValueError('Literal search requires 1–200 characters')
        offset = self.integer(action, 'offset', 0, 0, 1_000_000)
        start = self.integer(action, 'start_line', 1, 1, 10_000_000)
        limit = self.integer(action, 'limit', 20, 1, 40)
        paths = list(self.files(name))
        matches, skipped, size = [], [], 0
        for index in range(offset, min(len(paths), offset + 100)):
            filename = paths[index]
            try:
                lines, _ = self.lines(filename)
            except (ValueError, OSError, UnicodeError) as exc:
                skipped.append({'path': filename, 'error': str(exc)[:120]})
                if len(skipped) >= 10:
                    return self.search_result(action, matches, skipped, index + 1, 1, len(paths))
                continue
            for number in range(start if index == offset else 1, len(lines) + 1):
                line = lines[number - 1]
                if query not in line:
                    continue
                item = {'path': filename, 'line': number, 'text': line[:160],
                        'line_truncated': len(line) > 160}
                cost = len(json.dumps(item, ensure_ascii=False))
                if matches and (len(matches) >= limit or size + cost > 6000):
                    return self.search_result(action, matches, skipped, index, number, len(paths))
                matches.append(item); size += cost
        return self.search_result(action, matches, skipped, min(len(paths), offset + 100), 1, len(paths))

    @staticmethod
    def search_result(action, matches, skipped, offset, line, total):
        more = offset < total
        return {'matches': matches, 'skipped': skipped, 'truncated': more,
                'next_offset': offset, 'next_start_line': line,
                'next_action': {**action, 'offset': offset, 'start_line': line} if more else None,
                'note': 'Discovery snippets only, not read evidence. Follow next_action to avoid skipping matches.'}

    def batch(self, action):
        actions = action.get('actions')
        if (not isinstance(actions, list) or not 1 <= len(actions) <= 8
                or any(not isinstance(a, dict) or a.get('tool') not in ('read', 'search', 'list') for a in actions)):
            raise ValueError('batch requires 1–8 independent read/search/list actions; no nested batches')
        before = copy.deepcopy(self.reads)
        results = []
        for item in actions:
            results.append({'action': item, 'result': self.execute(item)})
            if len(json.dumps(results, ensure_ascii=False)) > 24000:
                self.reads = before
                return {'not_delivered': True, 'reason': 'batch_result_exceeds_24000_chars',
                        'instruction': 'Split this batch or narrow ranges; none of its new evidence was delivered.'}
        return {'results': results, 'note': 'Each result is independent; inspect errors. Only returned read results are evidence.'}

    @staticmethod
    def integer(action, key, default, low, high):
        value = action.get(key, default)
        if type(value) is not int or not low <= value <= high:
            raise ValueError(f'{key} must be an integer in [{low}, {high}]')
        return value
