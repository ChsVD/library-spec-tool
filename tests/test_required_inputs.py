import json
import tempfile
import unittest
from pathlib import Path
from stage1.task import run_task,Budgets,ReportPolicy
from stage1.reader import Reader
from stage1.contracts import check_evidence
from stage2.graph import new_graph,merge_discovery
from stage2.bundled import discovery_from_report
from stage2.context_cards import source_cards,compact_context
from stage2.required_inputs import plan

class RequiredDeliveryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.root=self.base/'input';self.root.mkdir()
        (self.root/'a.c').write_text('int x;\nint y;\n')
        self.source={'path':'a.c','start':1,'end':1}
        self.read={'tool':'read','path':'a.c','start':1,'count':1}
    def run_case(self,required,model,validator=lambda *_:[],artifacts=None,context=30000,factory=None):
        return run_task(self.root,self.base/'task',model,'fixture',validator,role='write',task_id='t',
            budgets=Budgets(calls=8,context_chars=context,reserve_chars=0,reserve_seconds=0),
            report_policy=ReportPolicy(1000,1000,1000,1000),required_inputs=required,
            artifacts=artifacts,reader_factory=factory,allow_report_patch=True)
    def test_each_role_receives_required_source_and_artifact_before_first_call(self):
        def model(messages,*_):
            self.assertTrue(any('int x;' in m['content'] for m in messages))
            self.assertTrue(any('module text' in m['content'] for m in messages))
            return json.dumps({'tool':'finish','report':{'ok':1}})
        def validate(r,reader,reads):
            self.assertIn('module',reads)
            return check_evidence([self.source],reader)
        result=self.run_case([{'tool':'artifact','id':'module'},self.read],model,validate,{'module':'module text'})
        self.assertEqual(result['status'],'task_completed',result)
        self.assertEqual(result['calls'],1);self.assertTrue(result['required_inputs']['complete'])
    def test_budget_gap_stops_before_model_and_records_pending_inputs(self):
        def never(*_):self.fail('model must not run')
        result=self.run_case([{'tool':'artifact','id':'large'},self.read],never,artifacts={'large':'x'*30000})
        self.assertEqual(result['status'],'needs_material');self.assertEqual(result['calls'],0)
        self.assertEqual(result['artifact_reads'],[])
        gap=json.loads((self.base/'task/material_gap.json').read_text())
        self.assertEqual(len(gap['pending_actions']),2)
    def test_blocked_source_delivery_rolls_back_credit(self):
        (self.root/'a.c').write_text('int x;\n'+'x'*6000+'\n');readers=[]
        def factory(root,log):
            reader=Reader(root,log);readers.append(reader);return reader
        result=self.run_case([self.read,dict(self.read,start=2)],lambda *_:self.fail('no model'),context=8000,factory=factory)
        self.assertEqual(result['status'],'needs_material')
        self.assertEqual(check_evidence([self.source],readers[0]),[])
        self.assertTrue(check_evidence([dict(self.source,start=2,end=2)],readers[0]))
    def test_missing_source_is_explicit_not_qcp_unsupported(self):
        result=self.run_case([dict(self.read,path='missing.c')],lambda *_:self.fail('no model'))
        self.assertEqual(result['reason'],'required_input_unavailable')
        self.assertNotEqual(result['status'],'tool_blocked')
    def test_new_unread_citation_stops_without_prose_retry(self):
        calls=[]
        def model(*_):calls.append(1);return json.dumps({'tool':'finish','report':{'evidence':[dict(self.source,start=2,end=2)]}})
        result=self.run_case([self.read],model,lambda r,reader,_:check_evidence(r['evidence'],reader))
        self.assertEqual(result['reason'],'report_requires_unread_evidence');self.assertEqual(len(calls),1)
        self.assertTrue((self.base/'task/report-attempt-1.json').exists());self.assertFalse((self.base/'task/report.json').exists())
    def test_plain_structure_error_still_allows_patch(self):
        actions=iter([{'tool':'finish','report':{'ok':0}},{'tool':'patch_report','changes':{'ok':1}}])
        result=self.run_case([self.read],lambda *_:json.dumps(next(actions)),lambda r,*_:[] if r['ok']==1 else ['bad value'])
        self.assertEqual(result['status'],'task_completed');self.assertEqual(result['calls'],2)
    def test_new_read_in_closing_stops_once(self):
        calls=[]
        def model(messages,*_):
            calls.append(1)
            if len(calls)==1:
                size=sum(len(m['content']) for m in messages)
                return json.dumps({'tool':'draft','draft':'x'*max(1,7500-size)})
            return json.dumps(dict(self.read,start=2))
        result=self.run_case([self.read],model,context=10000)
        self.assertEqual(result['reason'],'new_material_requested_during_closing',result)
        self.assertEqual(len(calls),2)

class RequiredPlanTests(unittest.TestCase):
    def test_review_includes_candidate_claim_evidence_and_neighbor(self):
        node={'id':'f','symbol':'f','source':{'path':'a.c','start':1,'end':2},'configuration':'test','materials':['module']}
        other={'id':'g','symbol':'g','source':{'path':'b.c','start':1,'end':1},'configuration':'test','materials':[]}
        graph=new_graph({'functions':[node,other]})
        graph['nodes']['g']['spec']={'candidate':True}
        graph['edges']['fg']={'id':'fg','caller':'f','callee':'g','callsite':node['source'],'condition':'always','certainty':'direct'}
        spec={'claims':[{'evidence':[{'path':'h.h','start':10,'end':12}]}]}
        _,cards=compact_context(graph,'f')
        artifacts={**cards,'source-index':[],'candidate':spec,'neighbor:g':{},'material:module:1':'one','material:module:2':'two'}
        result=plan(node,graph,artifacts,review=True,candidate=spec)
        ids={a['id'] for a in result if a['tool']=='artifact'}
        self.assertTrue({'candidate','neighbor:g','material:module:1','material:module:2'}<=ids)
        self.assertIn({'tool':'read','path':'h.h','start':10,'count':3},result)
        self.assertEqual(len(result),len({json.dumps(x,sort_keys=True) for x in result}))
