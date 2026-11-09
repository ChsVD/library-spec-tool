import json
from pathlib import Path
import tempfile
import unittest
from stage1.continue_saved import load_saved, validate_conditional_selection
from stage1.reader import Reader
from stage1.runner import snapshot
from stage1.report import SECTIONS

class ResumeTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.base=Path(self.tmp.name)
        self.root=self.base/'input'; (self.root/'openssl').mkdir(parents=True)
        (self.root/'openssl/a.c').write_text('fixture\n')
        self.prior=self.base/'old'; (self.prior/'modules').mkdir(parents=True)
        self.task=self.prior/'tasks/module-a';self.task.mkdir(parents=True)
        self.assigned={'id':'a','library':'openssl','scope':['openssl/a.c']}
        self.citation={'path':'openssl/a.c','start':1,'end':1}
        self.report={**self.assigned,'title':'A','depth':'detailed','sections':{s:'fixture' for s in SECTIONS},'evidence':[self.citation]}
        self.write(self.prior/'plan.json',{'modules':[self.assigned]})
        self.write(self.prior/'input_snapshot.json',snapshot(self.root))
        self.write(self.prior/'modules/a.json',self.report)
        self.write(self.task/'report.json',self.report)
        self.write(self.task/'status.json',{'status':'task_completed','role':'module','report':self.report})
        self.reader=Reader(self.root,self.base/'reads.jsonl')
        result=self.reader.execute({'tool':'read','path':'openssl/a.c'})
        (self.task/'conversation.jsonl').write_text(json.dumps({'role':'user','content':json.dumps(result)})+'\n')
    def tearDown(self):self.tmp.cleanup()
    def write(self,path,value):path.write_text(json.dumps(value))
    def test_saved_report_replayed_without_model_or_new_reads(self):
        _,modules,manifest=load_saved(self.root,self.prior)
        self.assertEqual(modules['a'],self.report);self.assertEqual(len(manifest),1)
        self.assertFalse((self.prior/'unused-replay-log.jsonl').exists())
    def test_changed_input_rejected(self):
        (self.root/'openssl/a.c').write_text('changed\n')
        with self.assertRaises(ValueError):load_saved(self.root,self.prior)
    def test_tampered_published_report_rejected(self):
        bad={**self.report,'title':'changed'};self.write(self.prior/'modules/a.json',bad)
        with self.assertRaises(ValueError):load_saved(self.root,self.prior)
    def test_unaccepted_report_rejected(self):
        self.write(self.task/'status.json',{'status':'validation_failed','role':'module','report':self.report})
        with self.assertRaises(ValueError):load_saved(self.root,self.prior)
    def test_withheld_evidence_not_credited(self):
        (self.task/'conversation.jsonl').write_text('')
        with self.assertRaises(ValueError):load_saved(self.root,self.prior)
    def test_conditional_selection_requires_explicit_conditions(self):
        plan={'modules':[{**self.assigned,'evidence':[self.citation]}]};frontier={'eligible':[]}
        report={'status':'tentative','primary':'a','rationale':'fixture','scope':'fixture subset','blockers':'unproved deps','evidence':[self.citation]}
        args={'plan':plan,'frontier':frontier}
        self.assertTrue(validate_conditional_selection(report,self.reader,{'plan','dependency_frontier'},**args))
        report['dependency_conditions']='requires unproved dependency; no proof authorized'
        self.assertEqual(validate_conditional_selection(report,self.reader,{'plan','dependency_frontier'},**args),[])
        report['status']='proposed'
        self.assertTrue(validate_conditional_selection(report,self.reader,{'plan','dependency_frontier'},**args))

    def test_resume_preserves_delivered_source_without_rereading(self):
        from stage1.task import run_task, Budgets
        from stage1.codex_backend import BackendError
        from stage1.contracts import check_evidence
        count=0
        def interrupted(messages,timeout):
            nonlocal count
            count+=1
            if count==1:return json.dumps({'tool':'read','path':'openssl/a.c','draft':'understood fixture'})
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
        (self.root/'openssl/a.c').write_text('changed\n')
        with self.assertRaises(ValueError):
            run_task(self.root,self.base/'bad-resume',resumed,'fixture',lambda *_:[],role='review',task_id='bad',budgets=budgets,resume_from=first)

    def test_backend_retry_is_bounded_and_counts_actual_calls(self):
        from stage1.task import run_task,Budgets
        from stage1.codex_backend import BackendError
        def fail(*_):raise BackendError('fixture unavailable')
        result=run_task(self.root,self.base/'retry',fail,'fixture',lambda *_:[],role='review',task_id='retry',budgets=Budgets(seconds=60,reserve_seconds=0),backend_retries=1)
        self.assertEqual(result['status'],'failed');self.assertEqual(result['calls'],2)
        self.assertEqual(len(result['backend_retry_events']),1)

if __name__=='__main__':unittest.main()
