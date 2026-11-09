"""Synthetic orchestration fixtures, never evidence of real library understanding."""
import copy
import json
from pathlib import Path
import tempfile
import threading
import time
import unittest

from stage1.task import Budgets, run_task
from stage1.report import SECTIONS


LIBS = ['openssl', 'sm2', 'mini-gmp']


class MultiFixtures(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.base = Path(self.temp.name)
        self.root = self.base / 'input'
        for lib in LIBS:
            directory = self.root / lib
            directory.mkdir(parents=True)
            (directory / 'sample.c').write_text(f'FIXTURE_PRIVATE_{lib}\nfixture only\n')
        self.budgets = Budgets(calls=40, seconds=60, reserve_seconds=0)

    def tearDown(self):
        self.temp.cleanup()

    def actions_model(self, actions):
        actions = iter(actions)
        def model(messages, timeout):
            return json.dumps(next(actions), ensure_ascii=False)
        return model

    def task(self, actions, name='task', validator=None, **kwargs):
        return run_task(self.root, self.base / name, self.actions_model(actions),
                        'Synthetic fixture task, not real analysis',
                        validator or (lambda *_: []), role='module', task_id=name,
                        budgets=kwargs.pop('budgets', self.budgets), **kwargs)

    def citation(self, lib):
        return {'path': f'{lib}/sample.c', 'start': 1, 'end': 2}

    def test_hard_context_limit_does_not_call_model(self):
        result = self.task([], budgets=Budgets(context_chars=1))
        self.assertEqual(result['status'], 'budget_exhausted')
        self.assertEqual(result['reason'], 'context_limit')
        self.assertEqual(result['calls'], 0)
        self.assertTrue((self.base / 'task/draft.json').exists())

    def test_budget_warning_preserves_semantic_draft_and_blocks_reads(self):
        seen = []
        actions = iter([
            {'tool': 'draft', 'draft': 'Fixture: content understood partially; missing dependency'},
            {'tool': 'read', 'path': 'openssl/sample.c'},
        ])
        def model(messages, timeout):
            seen.append(copy.deepcopy(messages))
            return json.dumps(next(actions))
        result = run_task(self.root, self.base / 'reserve', model, 'fixture', lambda *_: [],
                          role='module', task_id='reserve',
                          budgets=Budgets(calls=2, reserve_calls=1, reserve_seconds=0))
        self.assertEqual(result['reason'], 'call_limit')
        self.assertEqual(result['calls'], 2)
        self.assertIn('budget_warning', json.dumps(seen[-1]))
        draft = json.loads((self.base / 'reserve/draft.json').read_text())
        self.assertIn('missing dependency', draft['interpretation'])
        self.assertIn('error', draft['last_feedback'])
        self.assertFalse((self.base / 'reserve/reads.jsonl').exists())
        self.assertFalse(result['user_approved'])

    def test_missing_semantic_draft_cannot_keep_reading_forever(self):
        actions = [{'tool': 'read', 'path': 'openssl/sample.c'}] * 5
        result = self.task(actions, budgets=Budgets(calls=5, reserve_calls=0, reserve_seconds=0))
        reads = (self.base / 'task/reads.jsonl').read_text().splitlines()
        self.assertLessEqual(len(reads), 3)
        self.assertNotEqual(result['status'], 'task_completed')
        self.assertIn('draft', (self.base / 'task/conversation.jsonl').read_text())

    def test_empty_or_whitespace_draft_does_not_reset_required_interval(self):
        for index, empty in enumerate([{}, '', ' \t\n ']):
            with self.subTest(draft=empty):
                name = f'empty-draft-{index}'
                actions = [{'tool': 'read', 'path': 'openssl/sample.c', 'draft': empty}] * 5
                result = self.task(actions, name=name,
                                   budgets=Budgets(calls=5, reserve_calls=0, reserve_seconds=0))
                reads = (self.base / name / 'reads.jsonl').read_text().splitlines()
                self.assertEqual(len(reads), 3)
                self.assertEqual(result['reason'], 'call_limit')
                self.assertFalse(list((self.base / name).glob('draft-turn-*.json')))
                self.assertIn('this action was not executed',
                              (self.base / name / 'conversation.jsonl').read_text())

    def test_validation_retries_are_bounded_and_attempts_survive(self):
        result = self.task([{'tool': 'finish', 'report': {'fixture': i}} for i in range(3)],
                           validator=lambda *_: ['deliberately invalid fixture'],
                           budgets=Budgets(validation_retries=1))
        self.assertEqual(result['status'], 'validation_failed')
        self.assertEqual(result['reason'], 'validation_retry_limit')
        self.assertEqual(result['calls'], 2)
        self.assertEqual(len(list((self.base / 'task').glob('report-attempt-*.json'))), 2)
        self.assertFalse((self.base / 'task/report.json').exists())

    def test_validation_feedback_can_be_repaired(self):
        result = self.task([{'tool': 'finish', 'report': {}},
                            {'tool': 'finish', 'report': {'fixed': True}}],
                           validator=lambda report, *_: [] if report.get('fixed') else ['missing fixed'])
        self.assertEqual(result['status'], 'task_completed')
        self.assertFalse(result['user_approved'])

    def test_derived_artifact_does_not_become_original_evidence(self):
        observed = {}
        def validate(report, reader, artifact_reads):
            observed['sources'] = dict(reader.reads)
            observed['artifacts'] = set(artifact_reads)
            return []
        result = self.task([
            {'tool': 'artifact', 'id': 'module:source'},
            {'tool': 'artifact', 'id': '../private'},
            {'tool': 'finish', 'report': {'fixture': True}}], validator=validate,
            artifacts={'module:source': {'evidence': [self.citation('openssl')]}})
        self.assertEqual(result['status'], 'task_completed')
        self.assertEqual(observed['sources'], {})
        self.assertEqual(observed['artifacts'], {'module:source'})
        log = (self.base / 'task/conversation.jsonl').read_text()
        self.assertIn('derived_interpretation_not_original_evidence', log)
        self.assertIn('Unknown derived artifact', log)

    def test_oversized_material_preserves_closing_turn_without_evidence_credit(self):
        observed = {}
        def validate(report, reader, artifact_reads):
            observed['artifacts'] = set(artifact_reads)
            return []
        result = self.task([
            {'tool': 'artifact', 'id': 'huge'},
            {'tool': 'finish', 'report': {'fixture': 'incomplete; artifact not delivered'}}],
            validator=validate, artifacts={'huge': 'x' * 12000},
            budgets=Budgets(context_chars=10000, reserve_chars=5000))
        self.assertEqual(result['calls'], 2)
        self.assertEqual(observed['artifacts'], set())
        stored = list((self.base / 'task').glob('withheld-feedback-*.json'))
        self.assertEqual(len(stored), 1)
        self.assertIn('x' * 12000, stored[0].read_text())
        log = (self.base / 'task/conversation.jsonl').read_text()
        self.assertNotIn('x' * 12000, log)
        self.assertIn('not delivered', log)

    def test_late_response_cannot_claim_success(self):
        def slow(*_):
            time.sleep(.03)
            return '{"tool":"finish","report":{}}'
        result = run_task(self.root, self.base / 'late', slow, 'fixture', lambda *_: [],
                          role='module', task_id='late', budgets=Budgets(seconds=.01, reserve_seconds=0))
        self.assertEqual(result['status'], 'budget_exhausted')
        self.assertIn('time_limit', result['reason'])
        self.assertFalse((self.base / 'late/report.json').exists())

    def test_withheld_source_is_not_citable_but_remains_in_read_log(self):
        (self.root / 'openssl/sample.c').write_text('x' * 12000 + '\n')
        observed = {}
        def validate(report, reader, artifact_reads):
            observed['sources'] = dict(reader.reads)
            return []
        result = self.task([
            {'tool': 'read', 'path': 'openssl/sample.c'},
            {'tool': 'finish', 'report': {'fixture': 'incomplete; source not delivered'}}],
            validator=validate, budgets=Budgets(context_chars=10000, reserve_chars=5000))
        self.assertEqual(result['calls'], 2)
        self.assertFalse(observed['sources'].get('openssl/sample.c'))
        self.assertTrue((self.base / 'task/reads.jsonl').exists())
        self.assertEqual(len(list((self.base / 'task').glob('withheld-feedback-*.json'))), 1)

    def test_task_never_writes_under_input(self):
        with self.assertRaises(ValueError):
            run_task(self.root, self.root / 'output', lambda *_: '{}', 'fixture', lambda *_: [],
                     role='module', task_id='bad', budgets=self.budgets)

    def pipeline_fixture(self, *, extra_target=False, fail_module=None,
                         review_verdict='pass', plan_override=None, aggregate_override=None):
        """Names and contents deliberately carry no real OpenSSL interpretation."""
        coverage = {lib: {'mapped_areas': 'fixture only', 'unread_areas': 'real libraries not examined',
                         'configuration_unknowns': 'fixture unknown'} for lib in LIBS}
        entries = [{'id': f'fixture-{i}', 'library': lib, 'title': 'Synthetic module',
                    'scope': [f'{lib}/sample.c'], 'questions': 'Explain synthetic fixture only'}
                   for i, lib in enumerate(LIBS)]
        if extra_target:
            entries.append({'id': 'dynamic-extra', 'library': 'openssl', 'title': 'Additional synthetic module',
                            'scope': ['openssl/sample.c'], 'questions': 'Dynamic planner fixture'})
        plan = {'coverage': coverage, 'modules': entries,
                'evidence': [self.citation(lib) for lib in LIBS]}
        if plan_override:
            plan_override(plan)
        modules = {entry['id']: {
            'id': entry['id'], 'library': entry['library'], 'title': entry['title'], 'depth': 'detailed',
            'sections': {section: 'Fixture explanation; real semantics unknown' for section in SECTIONS},
            'evidence': [self.citation(entry['library'])]} for entry in entries}
        aggregate = {'module_ids': list(modules), 'coverage': coverage, 'gaps': [],
                     'rework': [], 'readiness': 'ready', 'evidence': []}
        if aggregate_override:
            aggregate_override(aggregate)
        comparison = {'comparisons': [{'id': 'synthetic-comparison', 'target': 'fixture-0',
            'reference': 'fixture-1', 'relation': 'unknown', 'basis': 'Fixture only',
            'differences': 'Not a semantic result', 'unknowns': 'All actual semantics unknown',
            'evidence': [self.citation('openssl'), self.citation('sm2')]}],
            'recommendation': {'confidence': 'tentative', 'primary': 'fixture-0', 'alternatives': [],
                'comparisons': ['synthetic-comparison'], 'rationale': 'Fixture only',
                'scope': 'openssl/sample.c', 'dependencies': 'unknown fixture',
                'reference_entries': 'sm2/sample.c', 'blockers': 'Not real analysis'}}
        review = {'verdict': review_verdict, 'coverage_checked': list(modules), 'findings': [],
                  'evidence': [self.citation(lib) for lib in LIBS]}
        created, histories = [], {}
        lock = threading.Lock()
        activity = {'active': 0, 'peak': 0}
        def factory(role, task_id):
            with lock:
                created.append((role, task_id))
            if role == 'planner':
                actions = [{'tool': 'read', 'path': f'{lib}/sample.c'} for lib in LIBS]
                report = plan
            elif role == 'module':
                ident = next((ident for ident in modules if ident in task_id), task_id)
                entry = modules[ident]
                actions = [{'tool': 'artifact', 'id': 'plan'},
                           {'tool': 'read', 'path': f'{entry["library"]}/sample.c'}]
                report = entry
            elif role in ('aggregate', 'comparison', 'review'):
                ids = [f'module:{ident}' for ident in modules]
                if role == 'aggregate':
                    ids += ['plan']
                if role in ('comparison', 'review'):
                    ids += ['aggregate']
                if role == 'review':
                    ids += ['comparison']
                actions = [{'tool': 'artifact', 'id': ident} for ident in ids]
                if role != 'aggregate':
                    actions += [{'tool': 'read', 'path': f'{lib}/sample.c'} for lib in LIBS]
                report = {'aggregate': aggregate, 'comparison': comparison, 'review': review}[role]
            else:
                raise AssertionError(f'Unexpected orchestration role: {role}')
            actions += [{'tool': 'finish', 'report': report}]
            for action in actions:
                action['draft'] = 'Synthetic finding; real semantics unknown; continue fixture actions'
            iterator = iter(actions)
            def model(messages, timeout):
                with lock:
                    histories.setdefault((role, task_id), []).append(copy.deepcopy(messages))
                    if role == 'module':
                        activity['active'] += 1
                        activity['peak'] = max(activity['peak'], activity['active'])
                try:
                    if role == 'module':
                        time.sleep(.015)
                        if fail_module and fail_module in task_id:
                            raise RuntimeError('Synthetic module failure')
                    return json.dumps(next(iterator, {'tool': 'finish', 'report': report}), ensure_ascii=False)
                finally:
                    if role == 'module':
                        with lock:
                            activity['active'] -= 1
            return model
        return factory, created, histories, activity

    def pipeline(self, factory, **kwargs):
        from stage1.multi import run_legacy_pipeline as run_pipeline
        return run_pipeline(self.root, self.base / 'pipeline', factory,
                            budgets=self.budgets, label='fixture', **kwargs)

    def test_pipeline_dispatches_dynamic_modules_and_independent_downstream_roles(self):
        factory, created, histories, activity = self.pipeline_fixture(extra_target=True)
        result = self.pipeline(factory, concurrency=2)
        self.assertEqual(result['status'], 'fixture_pipeline_complete', result)
        self.assertFalse(result['user_approved'])
        self.assertTrue(result['planned_modules_completed'])
        self.assertNotIn('full_coverage', result)
        saved_status = json.loads((self.base / 'pipeline/status.json').read_text())
        self.assertNotIn('full_coverage', saved_status)
        for filename in ['aggregate.md', 'comparison.md', 'independent-review.md',
                         'final/comparisons.md', 'final/recommendation.md', 'final/independent-review.md']:
            self.assertTrue((self.base / 'pipeline' / filename).is_file(), filename)
        comparison_text = (self.base / 'pipeline/comparison.md').read_text()
        self.assertIn('synthetic-comparison', comparison_text)
        self.assertIn('Not a semantic result', comparison_text)
        roles = [role for role, _ in created]
        self.assertEqual(roles.count('module'), 4)
        self.assertEqual(roles.count('comparison'), 1)
        self.assertEqual(roles.count('review'), 1)
        self.assertLess(roles.index('aggregate'), roles.index('comparison'))
        self.assertLess(roles.index('comparison'), roles.index('review'))
        self.assertLessEqual(activity['peak'], 2)
        self.assertGreaterEqual(activity['peak'], 2)
        for (role, ident), calls in histories.items():
            if role == 'module' and 'fixture-0' in ident:
                self.assertNotIn('FIXTURE_PRIVATE_sm2', json.dumps(calls))
                self.assertNotIn('FIXTURE_PRIVATE_mini-gmp', json.dumps(calls))
        logs = list((self.base / 'pipeline').rglob('reads.jsonl'))
        self.assertGreaterEqual(len(logs), 7)

    def test_failed_module_keeps_successes_and_prevents_false_complete(self):
        factory, created, _, _ = self.pipeline_fixture(fail_module='fixture-1')
        result = self.pipeline(factory, concurrency=2)
        self.assertNotIn(result['status'], ['fixture_pipeline_complete', 'pending_user_review'])
        self.assertFalse(result['user_approved'])

        saved = [json.loads(path.read_text()) for path in (self.base / 'pipeline').rglob('report.json')]
        self.assertTrue(any(report.get('id') == 'fixture-0' for report in saved))
        self.assertTrue(any(report.get('id') == 'fixture-2' for report in saved))
        self.assertFalse(any(role == 'comparison' for role, _ in created))

    def test_module_cap_never_silently_truncates_plan(self):
        factory, created, _, _ = self.pipeline_fixture(extra_target=True)
        result = self.pipeline(factory, max_modules=3)
        self.assertNotIn(result['status'], ['fixture_pipeline_complete', 'pending_user_review'])
        self.assertFalse(any(role == 'module' for role, _ in created))
        attempts = list((self.base / 'pipeline').rglob('report-attempt-*.json'))
        self.assertTrue(any(len(json.loads(path.read_text()).get('modules', [])) == 4 for path in attempts))

    def test_planner_missing_library_does_not_dispatch(self):
        def omit(plan):
            plan['modules'] = plan['modules'][:2]
        factory, created, _, _ = self.pipeline_fixture(plan_override=omit)
        result = self.pipeline(factory)
        self.assertNotEqual(result['status'], 'fixture_pipeline_complete')
        self.assertFalse(any(role == 'module' for role, _ in created))

    def test_review_cannot_approve_for_user(self):
        factory, _, _, _ = self.pipeline_fixture(review_verdict='needs_revision')
        result = self.pipeline(factory)
        self.assertNotIn(result['status'], ['fixture_pipeline_complete', 'pending_user_review'])
        self.assertFalse(result['user_approved'])
        # A rejected report must remain readable without opening raw JSON logs.
        for filename in ['aggregate.md', 'comparison.md', 'independent-review.md']:
            self.assertTrue((self.base / 'pipeline' / filename).is_file(), filename)
        self.assertIn('needs_revision', (self.base / 'pipeline/independent-review.md').read_text())
        self.assertFalse((self.base / 'pipeline/final/report.json').exists())

    def test_actual_module_contract_rejects_citations_only_seen_in_artifact(self):
        from stage1.contracts import validate_module
        assigned = {'id': 'synthetic', 'library': 'openssl'}
        report = {**assigned, 'title': 'Synthetic', 'depth': 'detailed',
                  'sections': {s: 'Fixture only' for s in SECTIONS},
                  'evidence': [self.citation('openssl')]}
        result = self.task([
            {'tool': 'artifact', 'id': 'module:source'},
            {'tool': 'finish', 'report': report}],
            artifacts={'module:source': report},
            budgets=Budgets(validation_retries=0),
            validator=lambda value, reader, reads: validate_module(value, reader, reads, task=assigned))
        self.assertEqual(result['status'], 'validation_failed')
        self.assertIn('not read by this role', (self.base / 'task/validation.jsonl').read_text())

    def test_rework_is_bounded_and_old_module_outputs_survive(self):
        def conflict(aggregate):
            aggregate['readiness'] = 'incomplete'
            aggregate['gaps'] = [{'kind': 'conflict', 'description': 'Synthetic persistent conflict',
                                 'module_ids': ['fixture-0'], 'blocking': True}]
            aggregate['rework'] = [{'module_id': 'fixture-0', 'reason': 'Synthetic reread request'}]
        factory, created, _, _ = self.pipeline_fixture(aggregate_override=conflict)
        result = self.pipeline(factory, max_rework_rounds=1)
        self.assertNotIn(result['status'], ['fixture_pipeline_complete', 'pending_user_review'])
        module_tasks = [ident for role, ident in created if role == 'module']
        self.assertEqual(len(module_tasks), 4)
        self.assertEqual(sum(role == 'aggregate' for role, _ in created), 2)
        self.assertFalse(any(role == 'comparison' for role, _ in created))
        versions = [path for path in (self.base / 'pipeline').rglob('report.json')
                    if json.loads(path.read_text()).get('id') == 'fixture-0']
        self.assertEqual(len(versions), 2)

    def test_comparison_failure_cannot_be_replaced_by_aggregate(self):
        factory, created, _, _ = self.pipeline_fixture()
        def failing_factory(role, ident):
            model = factory(role, ident)
            if role != 'comparison':
                return model
            def fail(*_):
                raise RuntimeError('Synthetic comparison failure')
            return fail
        result = self.pipeline(failing_factory)
        self.assertNotIn(result['status'], ['fixture_pipeline_complete', 'pending_user_review'])
        self.assertFalse(any(role == 'review' for role, _ in created))
        self.assertTrue((self.base / 'pipeline/aggregate.json').exists())
        self.assertFalse((self.base / 'pipeline/final/report.json').exists())

    def test_input_change_during_pipeline_invalidates_final_delivery(self):
        factory, _, _, _ = self.pipeline_fixture()
        def changing_factory(role, ident):
            model = factory(role, ident)
            def wrapped(messages, timeout):
                response = model(messages, timeout)
                if role == 'review' and json.loads(response).get('tool') == 'finish':
                    (self.root / 'new-fixture-file').write_text('simulated concurrent input change')
                return response
            return wrapped
        result = self.pipeline(changing_factory)
        self.assertEqual(result['status'], 'input_changed')
        self.assertFalse(result['user_approved'])
        self.assertFalse((self.base / 'pipeline/final/report.json').exists())

    def test_aggregate_must_read_plan_before_claiming_coverage(self):
        factory, _, _, _ = self.pipeline_fixture()
        def skipping_factory(role, ident):
            model = factory(role, ident)
            def wrapped(messages, timeout):
                response = model(messages, timeout)
                action = json.loads(response)
                if role == 'aggregate' and action.get('tool') == 'artifact' and action.get('id') == 'plan':
                    return json.dumps({'tool': 'draft', 'draft': 'Fixture skipped required plan'})
                return response
            return wrapped
        result = self.pipeline(skipping_factory)
        self.assertNotEqual(result['status'], 'fixture_pipeline_complete')
        errors = (self.base / 'pipeline/tasks/aggregate-r0/validation.jsonl').read_text()
        self.assertIn('plan', errors)
        self.assertFalse((self.base / 'pipeline/comparison.json').exists())

    def review_contract_fixture(self):
        from stage1.reader import Reader
        reader = Reader(self.root, self.base / 'review-reads.jsonl')
        modules = [{'id': f'fixture-{i}', 'library': lib,
                    'evidence': [self.citation(lib)]} for i, lib in enumerate(LIBS)]
        comparison = {'recommendation': {'primary': 'fixture-0'},
                      'comparisons': [{'evidence': [self.citation('openssl'), self.citation('sm2')]}]}
        review = {'verdict': 'pass', 'coverage_checked': [m['id'] for m in modules],
                  'findings': [], 'evidence': [self.citation(lib) for lib in LIBS]}
        artifacts = {'aggregate', 'comparison', *[f'module:{m["id"]}' for m in modules]}
        return reader, modules, comparison, review, artifacts

    def test_review_pass_rejects_unread_comparison_interval(self):
        from stage1.contracts import validate_review
        reader, modules, comparison, review, artifacts = self.review_contract_fixture()
        for lib in LIBS:
            reader.execute({'tool': 'read', 'path': f'{lib}/sample.c', 'start': 1, 'count': 1})
            for citation in review['evidence']:
                if citation['path'] == f'{lib}/sample.c':
                    citation['end'] = 1
        errors = validate_review(review, reader, artifacts, modules=modules, comparison=comparison)
        self.assertTrue(errors, 'Reviewer only read line 1; comparison also cites unread line 2')
        for lib in LIBS:
            reader.execute({'tool': 'read', 'path': f'{lib}/sample.c'})
        self.assertEqual(validate_review(review, reader, artifacts, modules=modules, comparison=comparison), [])

    def test_review_primary_requires_intersecting_interval_not_just_same_file(self):
        from stage1.contracts import validate_review
        reader, modules, comparison, review, artifacts = self.review_contract_fixture()
        for lib in LIBS:
            reader.execute({'tool': 'read', 'path': f'{lib}/sample.c'})
        modules[0]['evidence'][0]['end'] = 1
        review['evidence'][0]['start'] = 2
        errors = validate_review(review, reader, artifacts, modules=modules, comparison=comparison)
        self.assertTrue(errors, 'Review evidence on line 2 must not cover primary evidence only on line 1')
        review['evidence'][0]['start'] = 1
        self.assertEqual(validate_review(review, reader, artifacts, modules=modules, comparison=comparison), [])

    def test_normal_backend_timeout_preserves_time_for_closing(self):
        from stage1.codex_backend import BackendTimeout
        timeouts = []
        def model(messages, timeout):
            timeouts.append(timeout)
            if len(timeouts) == 1:
                raise BackendTimeout('Synthetic recoverable backend timeout')
            return json.dumps({'tool': 'finish', 'report': {'fixture': 'incomplete after timeout'}})
        result = run_task(self.root, self.base / 'timeout', model, 'fixture', lambda *_: [],
                          role='module', task_id='timeout',
                          budgets=Budgets(seconds=10, reserve_seconds=4))
        self.assertEqual(result['status'], 'task_completed', result)
        self.assertEqual(result['calls'], 2)
        self.assertLessEqual(timeouts[0], 6)
        self.assertGreater(timeouts[1], timeouts[0])
        self.assertTrue(result['closing'])
        self.assertFalse(result['user_approved'])

    def test_non_timeout_backend_error_remains_failure(self):
        from stage1.codex_backend import BackendError
        calls = []
        def model(*_):
            calls.append(True)
            raise BackendError('Synthetic configuration failure')
        result = run_task(self.root, self.base / 'backend-fail', model, 'fixture', lambda *_: [],
                          role='module', task_id='backend-fail', budgets=self.budgets)
        self.assertEqual(result['status'], 'failed')
        self.assertEqual(len(calls), 1)
        self.assertFalse((self.base / 'backend-fail/report.json').exists())

    def test_comparison_prompt_explains_enum_and_alternative_id_types(self):
        from stage1.multi import role_prompt
        prompt = role_prompt('comparison')
        for value in ['confidence', 'proposed', 'tentative', 'unable', 'alternatives']:
            self.assertIn(value, prompt)
        self.assertIn('字符串', prompt)
        self.assertIn('数组', prompt)

    def test_configured_long_timeout_used_for_normal_and_closing_calls(self):
        from stage1.codex_backend import BackendTimeout
        for cap in (600, 900):
            with self.subTest(cap=cap):
                seen = []
                def model(messages, timeout):
                    seen.append(timeout)
                    if len(seen) == 1:
                        raise BackendTimeout('Synthetic timeout; no actual wait')
                    return json.dumps({'tool': 'finish', 'report': {'fixture': True}})
                result = run_task(self.root, self.base / f'long-{cap}', model, 'fixture', lambda *_: [],
                                  role='planner', task_id='long',
                                  budgets=Budgets(seconds=2000, call_timeout_seconds=cap))
                self.assertEqual(result['status'], 'task_completed')
                self.assertEqual(seen, [cap, cap])
                self.assertEqual(result['backend_timeouts'][0]['timeout_seconds'], cap)

    def test_call_timeout_rejects_nonpositive_or_nonfinite(self):
        for cap in (0, -1, float('nan'), float('inf')):
            with self.subTest(cap=cap), self.assertRaises(ValueError):
                Budgets(call_timeout_seconds=cap)

    def test_versioned_drafts_survive_later_backend_failure(self):
        from stage1.codex_backend import BackendError
        count = 0
        def model(messages, timeout):
            nonlocal count
            count += 1
            if count == 1:
                return json.dumps({'tool': 'draft', 'draft': 'first partial module explanation'})
            if count == 2:
                return json.dumps({'tool': 'checkpoint', 'note': 'second partial explanation; missing invariant'})
            raise BackendError('Synthetic later failure')
        result = run_task(self.root, self.base / 'versions', model, 'fixture', lambda *_: [],
                          role='module', task_id='versions', budgets=self.budgets)
        target = self.base / 'versions'
        self.assertEqual(result['status'], 'failed')
        self.assertIn('missing invariant', (target / 'draft.md').read_text())
        old = json.loads((target / 'checkpoints/turn-0001-draft.json').read_text())
        self.assertEqual(old['content'], 'first partial module explanation')
        self.assertEqual(old['validation'], 'not_validated')
        self.assertIn('second partial', (target / 'checkpoints/turn-0002-note.md').read_text())
        self.assertFalse((target / 'report.json').exists())

    def test_rejected_report_is_saved_without_becoming_valid_output(self):
        result = self.task([{'tool': 'finish', 'report': {'incomplete': 'module body'}}],
                           validator=lambda *_: ['Missing source evidence'],
                           budgets=Budgets(validation_retries=0))
        target = self.base / 'task'
        self.assertEqual(result['status'], 'validation_failed')
        saved = json.loads((target / 'checkpoints/turn-0001-report.json').read_text())
        self.assertEqual(saved['content'], {'incomplete': 'module body'})
        self.assertEqual(saved['validation'], 'not_validated')
        self.assertTrue((target / 'checkpoints/turn-0001-report.md').exists())
        self.assertFalse((target / 'report.json').exists())

    def test_interruption_keeps_prior_checkpoint_and_readable_draft(self):
        count = 0
        def model(messages, timeout):
            nonlocal count
            count += 1
            if count == 1:
                return json.dumps({'tool': 'draft', 'draft': 'completed first section'})
            raise KeyboardInterrupt()
        result = run_task(self.root, self.base / 'cancel', model, 'fixture', lambda *_: [],
                          role='module', task_id='cancel', budgets=self.budgets)
        self.assertEqual(result['status'], 'interrupted')
        self.assertIn('completed first section', (self.base / 'cancel/draft.md').read_text())
        self.assertTrue((self.base / 'cancel/checkpoints/turn-0001-draft.json').exists())

    def test_atomic_write_failure_preserves_previous_complete_file(self):
        from unittest.mock import patch
        from stage1.task import write_json
        target = self.base / 'saved.json'
        write_json(target, {'content': 'previous complete version'})
        with patch.object(Path, 'replace', side_effect=OSError('Synthetic rename failure')):
            with self.assertRaises(OSError):
                write_json(target, {'content': 'new version'})
        self.assertEqual(json.loads(target.read_text())['content'], 'previous complete version')
        self.assertEqual(json.loads(target.with_suffix('.json.tmp').read_text())['content'], 'new version')


if __name__ == '__main__':
    unittest.main()
