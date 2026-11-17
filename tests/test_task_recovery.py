"""Generic task recovery and bounded backend retry regression checks."""
import json
from pathlib import Path
import tempfile
import unittest


class TaskRecoveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.base = Path(self.tmp.name)
        self.root = self.base / 'input'
        (self.root / 'target').mkdir(parents=True)
        (self.root / 'target/a.c').write_text('fixture\n')
        self.citation = {'path': 'target/a.c', 'start': 1, 'end': 1}

    def tearDown(self):
        self.tmp.cleanup()

    def test_resume_preserves_delivered_source_without_rereading(self):
        from stage1.task import run_task, Budgets
        from stage1.codex_backend import BackendError
        from stage1.contracts import check_evidence
        count=0
        def interrupted(messages,timeout):
            nonlocal count
            count+=1
            if count==1:return json.dumps({'tool':'read','path':'target/a.c','draft':'understood fixture'})
            raise BackendError('fixture interruption')
        budgets=Budgets(seconds=60,reserve_seconds=0)
        first=self.base/'first'
        stopped=run_task(self.root,first,interrupted,'fixture',lambda *_:[],role='review',task_id='first',budgets=budgets)
        self.assertEqual(stopped['status'],'failed')
        def resumed(messages,timeout):
            self.assertIn('fixture',json.dumps(messages))
            return json.dumps({'tool':'finish','report':{'evidence':[self.citation]}})
        result=run_task(self.root,self.base/'resumed',resumed,'fixture',lambda report,reader,_:check_evidence(report['evidence'],reader),role='review',task_id='resumed',budgets=budgets,resume_from=first)
        self.assertEqual(result['status'],'task_completed');self.assertEqual(result['calls'],1)
        self.assertEqual(result['previous_calls'],2)
        self.assertFalse((self.base/'resumed/reads.jsonl').exists())
        (self.root/'target/a.c').write_text('changed\n')
        with self.assertRaises(ValueError):
            run_task(self.root,self.base/'bad-resume',resumed,'fixture',lambda *_:[],role='review',task_id='bad',budgets=budgets,resume_from=first)

    def test_backend_retry_is_bounded_and_counts_actual_calls(self):
        from stage1.task import run_task,Budgets
        from stage1.codex_backend import BackendError
        def fail(*_):raise BackendError('fixture unavailable')
        result=run_task(self.root,self.base/'retry',fail,'fixture',lambda *_:[],role='review',task_id='retry',budgets=Budgets(seconds=60,reserve_seconds=0),backend_retries=1)
        self.assertEqual(result['status'],'failed');self.assertEqual(result['calls'],2)
        self.assertEqual(len(result['backend_retry_events']),1)

if __name__ == '__main__':
    unittest.main()
