import json
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path
from stage1.task import run_task, Budgets, ReportPolicy
from stage1.contracts import check_evidence

class ReportPolicyTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.root=self.base/'input';self.root.mkdir()
        (self.root/'a.c').write_text('int f(void) { return 1; }\n')
    def run_case(self,model,validator,context=20000,policy=None,**kw):
        return run_task(self.root,self.base/'task',model,'bounded fixture',validator,
            role='write',task_id='t',budgets=Budgets(calls=8,context_chars=context,reserve_seconds=0,reserve_chars=100),
            report_policy=policy or ReportPolicy(6000,2000,1000,3000),allow_report_patch=True,**kw)
    def test_over_context_complete_report_is_locally_validated_once(self):
        calls=[]
        def model(messages,timeout):
            calls.append(1)
            remaining=6000-sum(len(m['content']) for m in messages)
            return json.dumps({'tool':'finish','report':{'text':'x'*(remaining+100)}})
        result=self.run_case(model,lambda r,*_:[],context=6000,policy=ReportPolicy(10000,2000,1000,3000))
        self.assertEqual(result['status'],'task_completed',result)
        self.assertTrue(result['local_validation_after_context_limit']);self.assertEqual(len(calls),1)
        self.assertFalse(result['user_approved'])
    def test_over_context_invalid_evidence_never_gets_accepted_or_another_call(self):
        calls=[]
        def model(messages,timeout):
            calls.append(1)
            return json.dumps({'tool':'finish','report':{'text':'x'*(6100-sum(len(m['content']) for m in messages))}})
        def validator(report,reader,reads):return check_evidence([{'path':'a.c','start':1,'end':1}],reader)
        result=self.run_case(model,validator,context=6000,policy=ReportPolicy(10000,2000,1000,3000))
        self.assertEqual(result['reason'],'context_limit_report_invalid',result)
        self.assertEqual(len(calls),1);self.assertFalse((self.base/'task/report.json').exists())
        self.assertTrue((self.base/'task/validation.jsonl').exists())
    def test_parts_are_assembled_then_validated_as_one_report(self):
        actions=iter([{'tool':'report_part','fields':{'a':1}}, {'tool':'report_part','fields':{'b':2}}, {'tool':'finish'}])
        checked=[]
        def validator(r,*_):checked.append(r);return [] if r=={'a':1,'b':2} else ['missing field']
        result=self.run_case(lambda *_:json.dumps(next(actions)),validator)
        self.assertEqual(result['status'],'task_completed',result);self.assertEqual(checked,[{'a':1,'b':2}])
        self.assertTrue(list((self.base/'task/checkpoints').glob('*report-parts.json')))
    def test_report_limit_enforced_even_when_validator_passes(self):
        actions=iter([{'tool':'finish','report':{'text':'x'*1001}}, {'tool':'patch_report','changes':{'text':'short'}}])
        result=self.run_case(lambda *_:json.dumps(next(actions)),lambda *_:[],policy=ReportPolicy(1000,1000,1000,1000))
        self.assertEqual(result['status'],'task_completed',result);self.assertEqual(result['validation_failures'],1)
        self.assertEqual(result['report']['text'],'short')
    def test_output_and_repair_reserves_are_separate(self):
        actions=iter([{'tool':'finish','report':{'ok':1}}])
        result=self.run_case(lambda *_:json.dumps(next(actions)),lambda *_:[])
        self.assertEqual(result['effective_reserve_chars'],9000)
    def test_oversized_part_is_not_installed(self):
        actions=iter([{'tool':'report_part','fields':{'x':'x'*4000}}, {'tool':'finish'}])
        result=self.run_case(lambda *_:json.dumps(next(actions)),lambda r,*_:[] if isinstance(r,dict) else ['no report'])
        self.assertNotEqual(result['status'],'task_completed')
        self.assertFalse(list((self.base/'task/checkpoints').glob('*report-parts.json')))

    def test_local_validation_does_not_waive_time_limit(self):
        clock=[0.0]
        def model(*_):
            clock[0]=2000.0
            return json.dumps({'tool':'finish','report':{'ok':1}})
        with patch('stage1.task.time.monotonic',side_effect=lambda:clock[0]):
            result=self.run_case(model,lambda *_:[])
        self.assertEqual(result['reason'],'time_limit_after_response')
        self.assertFalse((self.base/'task/report.json').exists())
    def test_disabled_parts_cannot_supply_later_finish(self):
        actions=iter([{'tool':'report_part','fields':{'ok':1}}, {'tool':'finish'}])
        result=self.run_case(lambda *_:json.dumps(next(actions)),lambda r,*_:[] if r=={'ok':1} else ['missing'],allowed_tools={'finish'})
        self.assertNotEqual(result['status'],'task_completed')
        self.assertFalse(list((self.base/'task/checkpoints').glob('*report-parts.json')))
