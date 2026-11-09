import json
import tempfile
import unittest
from pathlib import Path
from stage1.report_parts import merge,fingerprint
from stage1.task import run_task,Budgets,ReportPolicy
from stage1.codex_backend import parse_events,BackendProtocolError


class BatchTests(unittest.TestCase):
    def run_case(self,actions,validator=lambda *_:[],calls=8):
        temp=tempfile.TemporaryDirectory();self.addCleanup(temp.cleanup)
        base=Path(temp.name);root=base/'input';root.mkdir();iterator=iter(actions)
        def model(*_):
            value=next(iterator)
            if isinstance(value,Exception):raise value
            return value if isinstance(value,str) else json.dumps(value)
        state=run_task(root,base/'task',model,'fixture',validator,role='write',task_id='t',
            budgets=Budgets(calls=calls,seconds=30,context_chars=30000,reserve_seconds=0,reserve_chars=0),
            report_policy=ReportPolicy(3000,1000,1000,1000,True),allow_report_patch=True)
        return state,base

    def test_appended_batches_replay_and_validate_as_whole(self):
        part={'tool':'report_part','batch_id':'a','append':{'claims':[{'id':'one'}]}}
        state,base=self.run_case([{'tool':'report_part','fields':{'function_id':'f'}},part,part,
            {'tool':'report_part','batch_id':'b','append':{'claims':[{'id':'two'}]}},{'tool':'finish'}],
            lambda r,*_:[] if r=={'function_id':'f','claims':[{'id':'one'},{'id':'two'}]} else ['wrong report'])
        self.assertEqual(state['status'],'task_completed',state)
        saved=json.loads((base/'task/report-parts.json').read_text())
        self.assertEqual(len(saved['batches']),2);self.assertFalse(saved['validated'])

    def test_conflicting_batch_or_type_is_not_committed(self):
        action={'batch_id':'one','append':{'claims':[1]}}
        ledger={'one':fingerprint(action)}
        with self.assertRaisesRegex(ValueError,'different content'):
            merge({'claims':[1]},{'batch_id':'one','append':{'claims':[2]}},ledger)
        with self.assertRaisesRegex(ValueError,'non-list'):
            merge({'claims':'bad'},action,{})
        self.assertEqual(ledger,{'one':fingerprint(action)})

    def test_interruption_keeps_saved_parts_without_candidate(self):
        state,base=self.run_case([{'tool':'report_part','batch_id':'a','append':{'claims':[1]}}],calls=1)
        self.assertEqual(state['status'],'budget_exhausted')
        self.assertTrue((base/'task/report-parts.json').exists())
        self.assertFalse((base/'task/report.json').exists())

    def test_invalid_full_report_never_accepted(self):
        state,base=self.run_case([{'tool':'report_part','fields':{'wrong':1}},{'tool':'finish'}],lambda *_:['missing sections'],calls=2)
        self.assertNotEqual(state['status'],'task_completed')
        self.assertFalse((base/'task/report.json').exists())

    def test_malformed_json_one_repair_with_position(self):
        state,base=self.run_case(['{"tool":',{'tool':'finish','report':{'ok':True}}])
        self.assertEqual(state['status'],'task_completed');self.assertEqual(state['calls'],2)
        diagnostic=json.loads((base/'task/format-error-1.json').read_text())
        self.assertIsNotNone(diagnostic['parse_error']['position'])
        self.assertEqual(diagnostic['response_excerpt'],'{"tool":')

    def test_second_format_error_stops(self):
        state,base=self.run_case(['bad','still bad'])
        self.assertEqual(state['reason'],'output_format_error');self.assertEqual(state['calls'],2)

    def test_backend_completed_invalid_message_can_be_repaired(self):
        events='\n'.join(json.dumps(x) for x in [
            {'type':'item.completed','item':{'type':'agent_message','text':'not JSON'}},{'type':'turn.completed'}])
        with self.assertRaises(BackendProtocolError) as caught:parse_events(events)
        state,base=self.run_case([caught.exception,{'tool':'finish','report':{'ok':True}}])
        self.assertEqual(state['status'],'task_completed')
        self.assertEqual(json.loads((base/'task/format-error-1.json').read_text())['response_excerpt'],'not JSON')

    def test_long_invalid_response_bounded_and_not_silently_repaired(self):
        state,base=self.run_case(['x'*9000])
        self.assertEqual(state['reason'],'output_format_error');self.assertEqual(state['calls'],1)
        diagnostic=json.loads((base/'task/format-error-1.json').read_text())
        self.assertEqual(len(diagnostic['response_excerpt']),8000);self.assertTrue(diagnostic['truncated'])

    def test_resume_restores_parts_and_replay_ledger(self):
        state,base=self.run_case([{'tool':'report_part','batch_id':'a','append':{'claims':[1]}}],calls=1)
        actions=iter([{'tool':'report_part','batch_id':'a','append':{'claims':[1]}},{'tool':'finish'}])
        resumed=run_task(base/'input',base/'resumed',lambda *_:json.dumps(next(actions)),'fixture',
            lambda r,*_:[] if r=={'claims':[1]} else ['duplicate or lost batch'],role='write',task_id='r',
            budgets=Budgets(calls=4,seconds=30,context_chars=30000,reserve_seconds=0,reserve_chars=0),
            report_policy=ReportPolicy(3000,1000,1000,1000,True),allow_report_patch=True,resume_from=base/'task')
        self.assertEqual(resumed['status'],'task_completed',resumed)

    def test_oversized_batch_rejected_without_losing_earlier_parts(self):
        state,base=self.run_case([
            {'tool':'report_part','fields':{'function_id':'f'}},
            {'tool':'report_part','batch_id':'large','append':{'claims':['x'*1100]}},
            {'tool':'report_part','batch_id':'small','append':{'claims':['small']}},
            {'tool':'finish'}],lambda r,*_:[] if r=={'function_id':'f','claims':['small']} else ['wrong assembly'])
        self.assertEqual(state['status'],'task_completed',state)
        ledger=json.loads((base/'task/report-parts.json').read_text())['batches']
        self.assertNotIn('large',ledger)
