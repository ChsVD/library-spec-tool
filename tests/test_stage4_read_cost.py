"""Fixed, local responses only: no model/backend invocations."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from stage1.contracts import check_evidence
from stage1.reader import Reader
from stage1.task import Budgets, run_task
from stage2.bundle_reader import reader_factory as bundled_reader
from stage4.read_cost import reader_factory, summarize_run


def test_overlap_digest_and_rollback(tmp_path):
    root = tmp_path / 'input'; root.mkdir()
    source = root / 'a.c'; source.write_text('one\ntwo\nthree\nfour\nfive\n')
    reader = reader_factory()(root, tmp_path / 'read.jsonl')
    assert [x['line'] for x in reader.execute({'tool': 'read', 'path': 'a.c', 'count': 3})['lines']] == [1, 2, 3]
    before = copy.deepcopy(reader.reads)
    action = {'tool': 'read', 'path': 'a.c', 'start': 2, 'count': 4}
    result = reader.execute(action)
    assert [x['line'] for x in result['lines']] == [4, 5]
    assert result['omitted_previously_delivered'] == [{'start': 2, 'end': 3}]
    assert not check_evidence([{'path': 'a.c', 'start': 1, 'end': 5}], reader)
    reader.reads = before  # same rollback as withheld-feedback in run_task
    assert [x['line'] for x in reader.execute(action)['lines']] == [4, 5]
    source.write_text('ONE\ntwo\nthree\nfour\nfive\n')
    assert [x['line'] for x in reader.execute(action)['lines']] == [2, 3, 4, 5]
    independent = reader_factory()(root, tmp_path / 'independent.jsonl')
    assert len(independent.execute(action)['lines']) == 4
    default = Reader(root, tmp_path / 'default.jsonl')
    default.execute(action)
    assert len(default.execute(action)['lines']) == 4


def test_bundle_boundaries_and_batch(tmp_path):
    root = tmp_path / 'input'; root.mkdir()
    bundle = tmp_path / 'bundle'; bundle.mkdir()
    data = b'aa\nbb\ncc\n'
    (bundle / 'copy.c').write_bytes(data)
    sha = hashlib.sha256(data).hexdigest()
    manifest = {'files': {'copy.c': sha}, 'mappings': [
        {'original': {'path': 'original.c', 'start': 5, 'end': 7},
         'bundle': {'path': 'copy.c', 'start': 1, 'end': 3}, 'sha256': sha}]}
    reader = reader_factory(bundled_reader([(bundle, manifest)]))(root, tmp_path / 'reads.jsonl')
    reader.execute({'tool': 'read', 'path': 'original.c', 'start': 5, 'count': 2})
    result = reader.execute({'tool': 'batch', 'actions': [
        {'tool': 'read', 'path': 'original.c', 'start': 6, 'count': 2},
        {'tool': 'read', 'path': 'original.c', 'start': 7, 'count': 1}]})
    assert result['results'][0]['result']['lines'] == [{'line': 7, 'text': 'cc'}]
    assert result['results'][1]['result']['lines'] == []
    assert 'not_extracted' in reader.execute({'tool': 'read', 'path': 'original.c', 'start': 4, 'count': 3})['error']
    (bundle / 'copy.c').write_text('changed')
    assert 'changed' in reader.execute({'tool': 'read', 'path': 'original.c', 'start': 5, 'count': 1})['error']


def _fixed_task(root, folder, reader, *, calls=2, resume_from=None):
    responses = iter([{'tool': 'read', 'path': 'a.c', 'start': 2, 'count': 3},
                      {'tool': 'finish', 'report': {'ok': True}}])
    return run_task(root, folder, lambda messages, timeout: json.dumps(next(responses)),
        'fixed local test', lambda report, reader, artifacts: [],
        role='common', task_id=folder.name,
        budgets=Budgets(calls=calls, reserve_calls=0, reserve_seconds=0, reserve_chars=0),
        reader_factory=reader, required_inputs=[{'tool': 'read', 'path': 'a.c', 'start': 1, 'count': 2}],
        resume_from=resume_from)


def test_real_sessions_ab_and_withheld_accounting(tmp_path):
    root = tmp_path / 'input'; root.mkdir()
    (root / 'a.c').write_text('aa\nbbb\ncccc\nddddd\n')
    baseline = tmp_path / 'baseline'; optimized = tmp_path / 'optimized'
    assert _fixed_task(root, baseline, None)['status'] == 'task_completed'
    assert _fixed_task(root, optimized, reader_factory())['status'] == 'task_completed'
    old = summarize_run(baseline)['totals']; new = summarize_run(optimized)['totals']
    assert old['calls'] == new['calls'] == 2
    assert old['first']['original'] == new['first']['original'] == 5
    assert old['later']['original'] == 12
    assert new['later']['original'] == 9
    assert old['within_role_repeat_original'] == 3
    assert new['within_role_repeat_original'] == 0
    # An actual attempted read log and withheld audit are not delivered materials.
    (optimized / 'withheld-feedback-9.json').write_text(json.dumps({'path': 'a.c', 'sha256': 'fake', 'lines': [{'line': 1, 'text': 'NEVER'}]}))
    assert summarize_run(optimized)['totals'] == new
    # Reconstruct exact wire character totals including escaped/envelope overhead.
    for folder in (baseline, optimized):
        summary = summarize_run(folder)['totals']
        messages = [json.loads(line) for line in (folder / 'conversation.jsonl').read_text().splitlines()]
        chars = len((folder / 'task.md').read_text()) + sum(len(m['content']) for m in messages if m['role'] != 'assistant')
        assert sum(summary[p][k] for p in ('first', 'later') for k in ('original', 'derived', 'prompt')) == chars


def test_resume_reconstructs_only_delivered_lines(tmp_path):
    root = tmp_path / 'input'; root.mkdir()
    (root / 'a.c').write_text('aa\nbbb\ncccc\nddddd\n')
    first = tmp_path / 'first'
    assert _fixed_task(root, first, reader_factory(), calls=1)['status'] == 'budget_exhausted'
    second = tmp_path / 'second'
    assert _fixed_task(root, second, reader_factory(), resume_from=first)['status'] == 'task_completed'
    messages = [json.loads(line) for line in (second / 'conversation.jsonl').read_text().splitlines()]
    # The replay's omitted line 2 plus delivered lines 3,4 reconstruct one full
    # evidence ledger, so resumed full overlap is handled without retransmission.
    assert any('already_delivered_source' in m['content'] for m in messages)
    previous_count = len((first / 'conversation.jsonl').read_text().splitlines())
    assert not any('"text": "' in m['content'] for m in messages[previous_count:])


def test_independent_roles_and_derived_are_distinct(tmp_path):
    root = tmp_path / 'input'; root.mkdir()
    (root / 'a.c').write_text('abc\ndef\n')
    for role in ('common', 'review'):
        responses = iter([{'tool': 'finish', 'report': {}}])
        run_task(root, tmp_path / 'run' / role, lambda messages, timeout: json.dumps(next(responses)),
            'fixed', lambda report, reader, artifacts: [], role=role, task_id=role,
            budgets=Budgets(reserve_seconds=0), artifacts={'card': {'claim': 'derived'}},
            reader_factory=reader_factory(), required_inputs=[{'tool': 'artifact', 'id': 'card'},
                {'tool': 'read', 'path': 'a.c', 'start': 1, 'count': 2}])
    report = summarize_run(tmp_path / 'run')
    assert report['totals']['within_role_repeat_original'] == 0
    assert report['totals']['independent_role_repeat_original'] == 6
    assert report['totals']['first']['derived'] == 2 * len(json.dumps({'claim': 'derived'}))


def test_original_reader_limits_and_batch_rollback(tmp_path):
    root = tmp_path / 'input'; root.mkdir()
    data = ('x' * 13000 + '\n' + 'y' * 13000 + '\n').encode()
    (root / 'a.c').write_bytes(data)
    read_both = {'tool': 'read', 'path': 'a.c', 'start': 1, 'count': 2}
    default = Reader(root, tmp_path / 'default.jsonl')
    wrapped = reader_factory()(root, tmp_path / 'wrapped.jsonl')
    assert wrapped.execute(read_both) == default.execute(read_both)
    # Parent traversal remains rejected by the underlying Reader.
    assert wrapped.execute({'tool': 'read', 'path': '../input/a.c'}) == default.execute({'tool': 'read', 'path': '../input/a.c'})
    fresh = reader_factory()(root, tmp_path / 'batch.jsonl')
    before = copy.deepcopy(fresh.reads)
    result = fresh.execute({'tool': 'batch', 'actions': [
        {'tool': 'read', 'path': 'a.c', 'start': 1, 'count': 1},
        {'tool': 'read', 'path': 'a.c', 'start': 2, 'count': 1}]})
    assert result['not_delivered']
    assert fresh.reads == before
    assert len(fresh.execute({'tool': 'read', 'path': 'a.c', 'start': 2, 'count': 1})['lines']) == 1
    bundle = tmp_path / 'bundle'; bundle.mkdir()
    (bundle / 'copy.c').write_bytes(data)
    sha = hashlib.sha256(data).hexdigest()
    manifest = {'files': {'copy.c': sha}, 'mappings': [
        {'original': {'path': 'a.c', 'start': 1, 'end': 2},
         'bundle': {'path': 'copy.c', 'start': 1, 'end': 2}, 'sha256': sha}]}
    factory = bundled_reader([(bundle, manifest)])
    original = factory(root, tmp_path / 'bundle-original.jsonl')
    filtered = reader_factory(factory)(root, tmp_path / 'bundle-filtered.jsonl')
    filtered.execute({'tool': 'read', 'path': 'a.c', 'start': 1, 'count': 1})
    # Even if one line is already known, the original BundleReader's whole
    # request character limit is preserved. Deduplication cannot waive it.
    assert filtered.execute(read_both) == original.execute(read_both)
    assert 'character limit' in filtered.execute(read_both)['error']


def test_invalid_run_and_unstarted_session(tmp_path):
    for folder in (tmp_path / 'missing', tmp_path):
        try:
            summarize_run(folder)
        except ValueError:
            pass
        else:
            raise AssertionError('Invalid run directory must not report zero costs')
    root = tmp_path / 'input'; root.mkdir()
    def no_model(messages, timeout):
        raise AssertionError('Mandatory material failure must happen before any model request')
    output = tmp_path / 'not-started'
    state = run_task(root, output, no_model, 'fixed', lambda r, reader, a: [],
        role='common', task_id='not-started', budgets=Budgets(),
        required_inputs=[{'tool': 'read', 'path': 'missing.c', 'start': 1, 'count': 1}])
    assert state['calls'] == 0
    report = summarize_run(output)
    assert not report['sessions'][0]['model_call_started']
    assert report['totals']['first_request_chars'] == 0
    assert report['totals']['sessions_without_model_call'] == 1


class ReadCostTests(unittest.TestCase):
    def run_fixture(self, fixture):
        with tempfile.TemporaryDirectory() as folder:
            fixture(Path(folder))

    def test_overlap_digest_and_rollback(self):
        self.run_fixture(test_overlap_digest_and_rollback)

    def test_bundle_boundaries_and_batch(self):
        self.run_fixture(test_bundle_boundaries_and_batch)

    def test_real_sessions_ab_and_withheld_accounting(self):
        self.run_fixture(test_real_sessions_ab_and_withheld_accounting)

    def test_resume_reconstructs_only_delivered_lines(self):
        self.run_fixture(test_resume_reconstructs_only_delivered_lines)

    def test_independent_roles_and_derived_are_distinct(self):
        self.run_fixture(test_independent_roles_and_derived_are_distinct)

    def test_original_reader_limits_and_batch_rollback(self):
        self.run_fixture(test_original_reader_limits_and_batch_rollback)

    def test_invalid_run_and_unstarted_session(self):
        self.run_fixture(test_invalid_run_and_unstarted_session)
