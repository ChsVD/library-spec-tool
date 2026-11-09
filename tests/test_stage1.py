import copy
import json
from pathlib import Path
import tempfile
import unittest

from stage1.reader import Reader
from stage1.report import SECTIONS, validate
from stage1.runner import APIModel, run


class Stage1Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.base = Path(self.tmp.name)
        self.root = self.base / 'input'
        self.root.mkdir()
        for library in ['openssl', 'sm2', 'mini-gmp']:
            (self.root / library).mkdir()
            (self.root / library / 'sample.c').write_text('line one\nline two\nline three\n')
        self.reader = Reader(self.root, self.base / 'reads.jsonl')

    def tearDown(self):
        self.tmp.cleanup()

    def report(self):
        libraries = ['openssl', 'sm2', 'mini-gmp']
        evidence = lambda lib: {'path': f'{lib}/sample.c', 'start': 1, 'end': 2}
        return {
            'coverage': {lib: {'mapped_areas': '夹具模块', 'unread_areas': '仅夹具', 'configuration_unknowns': '待确认'} for lib in libraries},
            'modules': [{'id': lib, 'library': lib, 'title': '夹具，不是真实库分析', 'depth': 'detailed',
                         'sections': {section: '待确认：夹具文本' for section in SECTIONS},
                         'evidence': [evidence(lib)]} for lib in libraries],
            'comparisons': [{'id': 'compare', 'target': 'openssl', 'reference': 'sm2', 'relation': 'unknown',
                             'basis': '夹具', 'differences': '待确认', 'unknowns': '夹具无法判断',
                             'evidence': [evidence('openssl'), evidence('sm2')]}],
            'recommendation': {'confidence': 'tentative', 'primary': 'openssl', 'alternatives': [],
                               'comparisons': ['compare'], 'rationale': '夹具', 'scope': 'sample.c',
                               'dependencies': '待确认', 'reference_entries': 'sm2/sample.c', 'blockers': '夹具'}
        }

    def read_all(self):
        for lib in ['openssl', 'sm2', 'mini-gmp']:
            self.reader.execute({'tool': 'read', 'path': f'{lib}/sample.c'})

    def test_read_pagination_and_log(self):
        result = self.reader.execute({'tool': 'read', 'path': 'openssl/sample.c', 'count': 2})
        self.assertTrue(result['truncated'])
        self.assertEqual(result['next_start'], 3)
        self.assertEqual(result['lines'][0]['line'], 1)
        self.assertEqual(len(self.reader.log.read_text().splitlines()), 1)

    def test_boundary_missing_directory_and_invalid_action(self):
        for action in [
            {'tool': 'read', 'path': '../outside'}, {'tool': 'read', 'path': '/etc/passwd'},
            {'tool': 'read', 'path': 'openssl/missing'}, {'tool': 'read', 'path': 'openssl'},
            {'tool': 'read', 'path': 'openssl/sample.c', 'start': 99},
            {'tool': 'read', 'path': 'openssl/sample.c', 'count': -1},
            {'tool': 'read', 'path': 'openssl/sample.c', 'start': True},
            {'tool': 'shell', 'command': 'echo unsafe'}]:
            with self.subTest(action=action):
                self.assertIn('error', self.reader.execute(action))

    def test_symlink_file_and_directory_escape(self):
        outside = self.base / 'outside'
        outside.mkdir()
        (outside / 'secret').write_text('OUTSIDE')
        (self.root / 'escape').symlink_to(outside, target_is_directory=True)
        (self.root / 'openssl' / 'escape').symlink_to(outside / 'secret')
        self.assertIn('error', self.reader.execute({'tool': 'read', 'path': 'escape/secret'}))
        self.assertIn('error', self.reader.execute({'tool': 'read', 'path': 'openssl/escape'}))
        search = self.reader.execute({'tool': 'search', 'query': 'OUTSIDE'})
        self.assertEqual(search['matches'], [])
        self.assertTrue(search['skipped'])
        (self.root / 'inside').symlink_to(self.root / 'openssl/sample.c')
        self.assertEqual(self.reader.execute({'tool': 'read', 'path': 'inside'})['path'], 'openssl/sample.c')

    def test_binary_encoding_and_long_line_are_explicit(self):
        for name, content in [('binary', b'abc\0def'), ('encoding', b'\xff'), ('long', b'x' * 24001)]:
            (self.root / name).write_bytes(content)
            self.assertIn('error', self.reader.execute({'tool': 'read', 'path': name}))

    def test_list_and_search_pagination(self):
        directory = self.root / 'pages'
        directory.mkdir()
        for i in range(105):
            (directory / f'{i:03}.txt').write_text('needle\n')
        result = self.reader.execute({'tool': 'list', 'path': 'pages'})
        self.assertTrue(result['truncated'])
        self.assertEqual(len(result['entries']), 100)
        result = self.reader.execute({'tool': 'search', 'path': 'pages', 'query': 'needle'})
        self.assertTrue(result['truncated'])
        found = list(result['matches'])
        while result['next_action']:
            self.assertLessEqual(len(result['matches']), 20)
            result = self.reader.execute(result['next_action'])
            found.extend(result['matches'])
        self.assertEqual(len(found), 105)
        self.assertEqual(len({x['path'] for x in found}), 105)

    def test_unread_or_changed_evidence_rejected(self):
        report = self.report()
        self.assertTrue(validate(report, self.reader))
        self.read_all()
        self.assertEqual(validate(report, self.reader), [])
        (self.root / 'openssl/sample.c').write_text('changed\nline two\nline three\n')
        self.assertTrue(any('input changed' in e for e in validate(report, self.reader)))

    def test_missing_sections_bad_links_and_line_ranges(self):
        self.read_all()
        report = self.report()
        del report['modules'][0]['sections'][SECTIONS[2]]
        report['comparisons'][0]['reference'] = 'nonexistent'
        report['recommendation']['primary'] = 'absent'
        report['modules'][1]['evidence'][0]['end'] = 300
        errors = validate(report, self.reader)
        self.assertGreaterEqual(len(errors), 4)

    def test_insufficient_material_is_a_valid_report_not_approval(self):
        self.read_all()
        report = self.report()
        report['comparisons'] = []
        report['recommendation'].update(confidence='unable', primary=None, comparisons=[])
        self.assertEqual(validate(report, self.reader), [])

    def test_fixture_flow_and_pending_review(self):
        actions = [{'tool': 'read', 'path': f'{lib}/sample.c'} for lib in ['openssl', 'sm2', 'mini-gmp']]
        actions += [{'tool': 'checkpoint', 'note': '夹具测试中间结果'}, {'tool': 'finish', 'report': self.report()}]
        status = self.run_actions(actions, 'success')
        self.assertEqual(status['status'], 'fixture_complete')
        review = json.loads((self.base / 'success/review.json').read_text())
        self.assertEqual(review['status'], 'pending_user_review')
        self.assertIsNone(review['selected_module'])
        self.assertTrue((self.base / 'success/modules/openssl.md').exists())
        self.assertTrue((self.base / 'success/comparisons.md').exists())
        self.assertTrue((self.base / 'success/checkpoints.md').exists())

    def run_actions(self, actions, name, **kwargs):
        iterator = iter(actions)
        def model(messages, timeout):
            return json.dumps(next(iterator), ensure_ascii=False)
        return run(self.root, self.base / name, model, 'fixture only', label='fixture', calls=20, **kwargs)

    def test_validation_feedback_can_be_repaired(self):
        actions = [{'tool': 'finish', 'report': self.report()}]
        actions += [{'tool': 'read', 'path': f'{lib}/sample.c'} for lib in ['openssl', 'sm2', 'mini-gmp']]
        actions += [{'tool': 'finish', 'report': self.report()}]
        status = self.run_actions(actions, 'repair')
        self.assertEqual(status['status'], 'fixture_complete')
        self.assertTrue((self.base / 'repair/validation.jsonl').exists())

    def test_codex_mode_uses_pending_review_not_fixture_status(self):
        # Mocked model: tests status routing only, not a real connectivity claim.
        actions = iter([{'tool': 'read', 'path': f'{lib}/sample.c'} for lib in ['openssl', 'sm2', 'mini-gmp']] +
                       [{'tool': 'finish', 'report': self.report()}])
        status = run(self.root, self.base / 'codex-status', lambda *_: json.dumps(next(actions)),
                     'mocked status test', label='real_codex')
        self.assertEqual(status['status'], 'pending_user_review')
        self.assertFalse(status['user_approved'])

    def test_budget_failure_and_retry_limits(self):
        status = run(self.root, self.base / 'budget', lambda *_: '{"tool":"checkpoint","note":"partial"}',
                     'fixture', calls=1, label='fixture')
        self.assertEqual(status['status'], 'budget_exhausted')
        status = self.run_actions([{'tool': 'finish', 'report': {}}], 'invalid', revisions=0)
        self.assertEqual(status['status'], 'validation_failed')
        def broken(*_):
            raise RuntimeError('secret value must never be logged')
        status = run(self.root, self.base / 'broken', broken, 'fixture', label='fixture')
        self.assertEqual(status['status'], 'failed')
        self.assertNotIn('secret', json.dumps(status))

    def test_output_cannot_be_written_under_input(self):
        with self.assertRaises(ValueError):
            run(self.root, self.root / 'output', lambda *_: '{}', 'fixture')

    def test_context_budget_prevents_model_call(self):
        def forbidden(*_):
            self.fail('Model must not be called after context limit')
        status = run(self.root, self.base / 'context', forbidden, 'long task', context_chars=1, label='fixture')
        self.assertEqual(status['status'], 'budget_exhausted')
        self.assertEqual(status['calls'], 0)

    def test_changed_input_after_reads_is_not_accepted(self):
        actions = iter([{'tool': 'read', 'path': f'{lib}/sample.c'} for lib in ['openssl', 'sm2', 'mini-gmp']])
        def model(*_):
            action = next(actions, None)
            if action is None:
                (self.root / 'new-file').write_text('concurrent input addition')
                action = {'tool': 'finish', 'report': self.report()}
            return json.dumps(action)
        status = run(self.root, self.base / 'changed', model, 'fixture', label='fixture')
        self.assertEqual(status['status'], 'input_changed')
        self.assertFalse((self.base / 'changed/report.json').exists())

    def test_recommendation_cannot_link_unrelated_comparison(self):
        self.read_all()
        report = self.report()
        another = copy.deepcopy(report['modules'][0])
        another['id'] = 'other-target'
        report['modules'].append(another)
        report['recommendation']['primary'] = 'other-target'
        self.assertTrue(any('same module' in e for e in validate(report, self.reader)))

    def test_object_alternatives_return_actionable_errors_without_throwing(self):
        self.read_all()
        report = self.report()
        report['recommendation']['alternatives'] = [{'id': 'openssl', 'reason': 'fixture malformed alternative'}]
        report['recommendation']['confidence'] = 'high'
        errors = validate(report, self.reader)
        self.assertTrue(any('alternatives' in error for error in errors), errors)
        self.assertTrue(any('confidence' in error for error in errors), errors)
        self.assertFalse(any('Malformed report' in error for error in errors), errors)

    def test_api_requires_safe_explicit_endpoint(self):
        for endpoint in ['http://example.com', 'https://user:secret@example.com', 'https://example.com/?key=secret']:
            with self.assertRaises(ValueError):
                APIModel(endpoint, 'model', 'key')


if __name__ == '__main__':
    unittest.main()
