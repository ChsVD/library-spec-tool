import copy
import json
from pathlib import Path
import tempfile
import unittest
from stage1.reader import Reader
from stage1.task import Budgets, write_json
from stage2.pipeline import run_pipeline as run_stage2
from stage2.graph import digest
from stage4.pipeline import run_pipeline, load_upstream
from stage4 import contracts
from tests.test_stage2_inventory import selected, GroupModel


def extract(ident):
    return {'function_id':ident,'proof_status':'not_proved','analysis':'integer identity needs',
            'categories':{k:{'status':'needed' if k=='mathematical_model' else 'not_applicable','reason':'fixture scalar identity'} for k in contracts.CATEGORIES},
            'needs':[{'id':'identity-need','spec_clause':'Ensure return=x','use_site':'return expression','scope':'shared','name':'identity','purpose':'postcondition','proposed_statement':'identity(x)=x','assumptions':'x integer',
                      'evidence':[{'path':'lib/code.c','start':1,'end':3}]}]}


def proposal(ids):
    return {'proof_status':'not_proved','references':[],'items':[{'id':'identity','kind':'definition','name':'identity','parameters':'x integer',
        'assumptions':'none','statement':'identity(x)=x','purpose':'scalar model','origin':'new_candidate','adaptation':'new model',
        'evidence':[],'used_by':ids,'depends_on':[],'validation_obligations':[{'id':'meaning','kind':'semantic_property','purpose':'identity meaning',
        'method':'unfold identity','environment':'Coq version to confirm','success_criterion':'forall x, identity x = x',
        'status':'planned','reason':'','evidence':[]}],'validation_plan':'check zero and signed values','proof_status':'not_proved'}],
        'coverage':{i:{'needs':[{'index':0,'action':'new','reference_ids':[],'item_ids':['identity'],'explanation':'identity requirement','unresolved':''}],
                      'categories':{k:{'status':'covered' if k=='mathematical_model' else 'not_applicable',
                                       'reason':'scalar fixture','item_ids':['identity'] if k=='mathematical_model' else []} for k in contracts.CATEGORIES}} for i in ids},
        'unknowns':[]}


def review(verdict='pass'):
    return {'proof_status':'not_proved','verdict':verdict,'checks':{k:'fixture check with source' for k in contracts.CHECKS},
            'findings':[] if verdict=='pass' else [{'description':'clarify integer range','blocking':True}],
            'evidence':[{'path':'lib/code.c','start':1,'end':3}],'tool_evidence':[]}


class Model:
    def __init__(self,role,revise=False):self.role=role;self.revise=revise
    def __call__(self,messages,timeout):
        system=messages[0]['content'];a=json.loads(system.split('任务：\n')[1].split('\n\nTask budgets:')[0])
        ids=json.loads(system.split('Derived artifact IDs: ')[1]);delivered=[];read=False;candidate=None;source_lines=set()
        required_lines=(set(range(a['function']['source']['start'],a['function']['source']['end']+1))
                        if self.role=='extract' and 'source-index' in ids else {1,2,3})
        for m in messages[1:]:
            if m['role']!='user':continue
            try:v=json.loads(m['content'])
            except ValueError:continue
            if v.get('kind')=='derived_interpretation_not_original_evidence':
                delivered.append(v['id'])
                if v['id']=='candidate':candidate=v['content']
            if v.get('path')=='lib/code.c' and v.get('lines'):
                source_lines.update(x['line'] for x in v['lines'])
                read=required_lines <= source_lines
        for ident in ids:
            if ident not in delivered:return json.dumps({'tool':'artifact','id':ident,'draft':'checked derived material, need original source'})
        if not read:return json.dumps({'tool':'read','path':'lib/code.c','start':1,'count':3,'draft':'check source'})
        if self.role=='extract':r=extract(a['function']['id'])
        elif self.role=='common':
            r=proposal(a['functions'])
            if self.revise and 'revision_review' not in ids:r['items'][0]['parameters']='unclear'
        else:r=review('needs_revision' if candidate['items'][0]['parameters']=='unclear' else 'pass')
        return json.dumps({'tool':'finish','report':r})


class Stage3Tests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.base=Path(self.tmp.name);self.root=self.base/'input'
        (self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text('int a(int x) { return b(x); }\nint b(int x) { return x; }\nint unrelated(int x) { return x+1; }\n')
        self.budgets=Budgets(calls=24,seconds=30,context_chars=60000,reserve_seconds=0)
        self.upstream=self.base/'stage2'
        result=run_stage2(self.root,self.upstream,selected(),{'module':'fixture module'},lambda r,t:GroupModel(r,t),budgets=self.budgets)
        self.assertEqual(result['status'],'candidates_reviewed')
        self.graph,self.nodes,_=load_upstream(self.root,self.upstream)
        self.ids=list(self.nodes);self.extracts={i:extract(i) for i in self.ids}
        self.reader=Reader(self.root,self.base/'reads.jsonl');self.reader.execute({'tool':'read','path':'lib/code.c','start':1,'count':3})
        self.reads={'extract:'+i for i in self.ids}|{'spec:'+i for i in self.ids}
    def tearDown(self):self.tmp.cleanup()
    def run_common(self,**kwargs):
        factory=kwargs.pop('factory',lambda r,t:Model(r))
        return run_pipeline(self.root,self.base/'common',self.upstream,factory,budgets=self.budgets,protocol_version=2,**kwargs)
    def validate(self,r):return contracts.candidate(r,self.reader,self.reads,nodes=self.nodes,extracts=self.extracts)
    def test_complete_group_chain_and_saved_outputs(self):
        result=self.run_common();self.assertEqual(result['status'],'common_candidates_reviewed')
        self.assertEqual(set(result['extracted_functions']),set(self.ids))
        self.assertTrue((self.base/'common/candidate.md').exists())
        self.assertEqual(len(list((self.base/'common/functions').glob('*/common_needs.json'))),3)
        self.assertEqual(len(result['tasks']),5)
    def test_fixed_categories_are_not_mandatory(self):
        r=proposal(self.ids);del r['coverage'][self.ids[0]]['categories']['capacity']
        self.assertEqual(self.validate(r),[])
    def test_omitted_function_and_need_rejected(self):
        r=proposal(self.ids);del r['coverage'][self.ids[0]];self.assertTrue(self.validate(r))
        r=proposal(self.ids);r['coverage'][self.ids[0]]['needs']=[];self.assertTrue(self.validate(r))
    def test_original_spec_needs_also_mapped(self):
        self.nodes[self.ids[0]]['spec']['common_needs']=[{'name':'extra','purpose':'extra','status':'needed_not_proved'}]
        self.assertTrue(self.validate(proposal(self.ids)))
    def test_bad_dependency_cycle_and_claimed_proof_rejected(self):
        r=proposal(self.ids);r['items'][0]['depends_on']=['missing'];self.assertTrue(self.validate(r))
        r=proposal(self.ids);r['items'][0]['proof_status']='proved';self.assertTrue(self.validate(r))
        r=proposal(self.ids);other=copy.deepcopy(r['items'][0]);other['id']='other';other['depends_on']=['identity']
        r['items'][0]['depends_on']=['other'];r['items'].append(other);self.assertTrue(self.validate(r))
    def test_original_evidence_must_be_read(self):
        r=proposal(self.ids);r['items'][0].update(origin='adapted',evidence=[{'path':'lib/code.c','start':99,'end':99}])
        self.assertTrue(self.validate(r))
    def test_unresolved_coverage_cannot_pass(self):
        r=proposal(self.ids);r['coverage'][self.ids[0]]['categories']['capacity'].update(status='unresolved')
        self.assertTrue(contracts.review(review(),self.reader,self.reads|{'candidate'},proposal=r,nodes=self.nodes))
    def test_review_must_read_sources_and_each_spec(self):
        reader=Reader(self.root,self.base/'empty.jsonl')
        self.assertTrue(contracts.review(review(),reader,{'candidate'},proposal=proposal(self.ids),nodes=self.nodes))
    def test_unknown_tool_support_is_not_unsupported(self):
        self.assertTrue(contracts.review(review('tool_blocked'),self.reader,self.reads|{'candidate'},proposal=proposal(self.ids),nodes=self.nodes))
    def test_review_revision_is_bounded_and_saved(self):
        result=self.run_common(factory=lambda r,t:Model(r,revise=True));self.assertEqual(result['status'],'common_candidates_reviewed')
        self.assertEqual(len(result['tasks']),7)
        self.assertEqual(json.loads((self.base/'common/candidate.json').read_text())['items'][0]['parameters'],'x integer')
    def test_partial_failure_resume_preserves_extractions(self):
        count=[0]
        def factory(r,t):
            if r=='extract':count[0]+=1
            if count[0]==2:
                class Fail:
                    def __call__(self,*a,**k):raise RuntimeError('fixture interruption')
                return Fail()
            return Model(r)
        result=self.run_common(factory=factory);self.assertEqual(result['status'],'incomplete')
        self.assertEqual(len(result['extracted_functions']),1)
        result=self.run_common(resume=True);self.assertEqual(result['status'],'common_candidates_reviewed')
        self.assertEqual(len(result['tasks']),6)
        def fail(*a):raise AssertionError('completed resume should not call models')
        self.assertEqual(self.run_common(resume=True,factory=fail)['status'],'common_candidates_reviewed')
    def test_incomplete_stage2_rejected(self):
        path=self.upstream/'status.json';s=json.loads(path.read_text());s['status']='incomplete';write_json(path,s)
        with self.assertRaises(ValueError):self.run_common()
    def test_changed_input_and_resume_checkpoint_rejected(self):
        self.run_common();path=self.base/'common/checkpoint.json';d=json.loads(path.read_text());d['extracts']={};write_json(path,d)
        with self.assertRaisesRegex(ValueError,'mismatch'):self.run_common(resume=True)
        (self.root/'lib/code.c').write_text('changed')
        with self.assertRaisesRegex(ValueError,'input differs'):self.run_common(resume=True)
    def test_malformed_links_report_errors(self):
        for field in ('used_by','depends_on'):
            r=proposal(self.ids);r['items'][0][field]=[{}];self.assertTrue(self.validate(r))
        r=proposal(self.ids);r['coverage'][self.ids[0]]['needs'][0]['item_ids']=[{}]
        self.assertTrue(self.validate(r))
    def test_upstream_status_change_during_task_stops(self):
        def factory(r,t):
            s=json.loads((self.upstream/'status.json').read_text());s['status']='incomplete';write_json(self.upstream/'status.json',s)
            return Model(r)
        self.assertEqual(self.run_common(factory=factory)['status'],'incomplete')
    def test_cli_automatically_hands_complete_group_to_stage3(self):
        from unittest.mock import patch
        from stage2.legacy_cli import main
        argv=['stage2','--manifest','fixture','--output',str(self.base/'cli'),'--with-common','--workflow','legacy']
        with patch('sys.argv',argv), patch('stage2.legacy_cli.load_manifest',return_value=({'selection_inventory':{}},{})), patch('stage1.codex_backend.CodexModel'), patch('stage2.legacy_cli.run_pipeline',return_value={'status':'candidates_reviewed'}), patch('stage4.pipeline.run_pipeline',return_value={'status':'common_candidates_reviewed'}) as downstream, patch('builtins.print'):
            self.assertEqual(main(),0);downstream.assert_called_once()
    def test_cli_never_hands_partial_group_to_stage3(self):
        from unittest.mock import patch
        from stage2.legacy_cli import main
        argv=['stage2','--manifest','fixture','--output',str(self.base/'cli'),'--with-common','--workflow','legacy']
        with patch('sys.argv',argv), patch('stage2.legacy_cli.load_manifest',return_value=({'selection_inventory':{}},{})), patch('stage1.codex_backend.CodexModel'), patch('stage2.legacy_cli.run_pipeline',return_value={'status':'incomplete'}), patch('stage4.pipeline.run_pipeline') as downstream, patch('builtins.print'):
            self.assertEqual(main(),1);downstream.assert_not_called()
    def test_upstream_modified_during_task_does_not_publish(self):
        first=[True]
        def factory(r,t):
            if first[0]:
                first[0]=False;g=copy.deepcopy(self.graph);g['coverage']='changed';write_json(self.upstream/'graph.json',g)
            return Model(r)
        self.assertEqual(self.run_common(factory=factory)['status'],'incomplete')
        self.assertFalse((self.base/'common/candidate.json').exists())

if __name__=='__main__':unittest.main()
