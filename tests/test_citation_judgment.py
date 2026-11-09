import json
import tempfile
import unittest
from pathlib import Path
from stage2.source_bundle import materialize
from stage2.bundle_reader import reader_factory
from stage1.task import run_task, Budgets, ReportPolicy
from stage1.contracts import check_evidence
from stage1.evidence_completion import citation_feedback


class CitationJudgmentTests(unittest.TestCase):
    def run_case(self, response='split', calls=4, context=20000, padding=0):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup)
        base=Path(tmp.name);root=base/'input';root.mkdir()
        (root/'a.c').write_text('int x;\nimportant omitted line\nint y;\n')
        first={'path':'a.c','start':1,'end':1};last={'path':'a.c','start':3,'end':3}
        manifest=materialize(root,base/'bundle',{'id':'f','source':first},
            {'snippets':[{'kind':'definition','symbol':'y','source':last}]})
        factory=reader_factory([(base/'bundle',manifest)]);readers=[];seen=[]
        def capture(root,log):
            reader=factory(root,log);readers.append(reader);return reader
        def model(messages,*_):
            seen.append(messages.copy())
            if len(seen)==1 or response=='repeat':
                return json.dumps({'tool':'finish','report':{'evidence':[{'path':'a.c','start':1,'end':3}]},'draft':'x'*padding, 'citation_judgment':'Keep the original range'})
            if response=='missing':return json.dumps({'tool':'needs_material','reason':'Middle line affects the claim'})
            if response=='read':return json.dumps({'tool':'read','path':'a.c','start':2,'count':1})
            return json.dumps({'tool':'patch_report','changes':{'evidence':[first,last]},
                               'citation_judgment':'The separate declarations support the claim; no claim relies on the omitted line.'})
        state=run_task(root,base/'task',model,'test',lambda report,reader,_:check_evidence(report['evidence'],reader),
            role='write',task_id='t',budgets=Budgets(calls=calls,seconds=30,context_chars=context,reserve_seconds=0,reserve_chars=0),
            required_inputs=[{'tool':'read','path':'a.c','start':n,'count':1} for n in (1,3)],
            report_policy=ReportPolicy(1000,1000,1000,1000),reader_factory=capture,
            complete_bundle_evidence=True,allow_report_patch=True)
        return state,base,readers[0],seen

    def test_split_citation_is_model_repair_not_program_trim(self):
        state,base,reader,seen=self.run_case()
        self.assertEqual(state['status'],'task_completed',state);self.assertEqual(state['calls'],2)
        audit=json.loads((base/'task/citation_judgment.json').read_text())
        issue=audit['feedback']['citation_judgment'][0]
        self.assertEqual(issue['available_intervals'],[[1,1],[3,3]])
        self.assertEqual(issue['delivered_intervals'],[[1,1],[3,3]])
        self.assertEqual(issue['missing_intervals'],[[2,2]])
        self.assertEqual(audit['response_action'],'patch_report')
        self.assertTrue(check_evidence([{'path':'a.c','start':2,'end':2}],reader))
        self.assertEqual(json.loads((base/'task/report-attempt-1.json').read_text())['evidence'][0]['end'],3)

    def test_substantive_missing_source_stops(self):
        state,base,reader,_=self.run_case('missing')
        self.assertEqual(state['status'],'needs_material');self.assertEqual(state['calls'],2)
        self.assertFalse((base/'task/report.json').exists())
        self.assertNotIn(2,reader.content['a.c'])

    def test_second_invalid_citation_does_not_loop(self):
        state,base,reader,_=self.run_case('repeat')
        self.assertEqual(state['status'],'needs_material');self.assertEqual(state['calls'],2)
        self.assertFalse((base/'task/report.json').exists())

    def test_repair_cannot_read_original(self):
        state,base,reader,_=self.run_case('read')
        self.assertEqual(state['status'],'needs_material');self.assertEqual(state['calls'],2)
        self.assertNotIn(2,reader.content['a.c'])

    def test_no_call_budget_no_repair(self):
        state,base,reader,_=self.run_case(calls=1)
        self.assertEqual(state['status'],'needs_material');self.assertEqual(state['calls'],1)
        audit=json.loads((base/'task/citation_judgment.json').read_text())
        self.assertFalse(audit['delivered'])

    def test_context_budget_preserves_final_report_space(self):
        state,base,reader,_=self.run_case(context=6000,padding=1500)
        self.assertEqual(state['status'],'needs_material');self.assertEqual(state['calls'],1)
        audit=json.loads((base/'task/citation_judgment.json').read_text())
        self.assertFalse(audit['delivered'])
        self.assertEqual(audit['reason'],'repair_budget_insufficient')

    def test_pathological_interval_is_not_expanded(self):
        _,_,reader,_=self.run_case()
        self.assertIsNone(citation_feedback({'evidence':[{'path':'a.c','start':1,'end':999999999}]},reader))
        self.assertIsNone(citation_feedback({'evidence':[{'path':'a.c','start':1,'end':3}]},reader,max_chars=10))
