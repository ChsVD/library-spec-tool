import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from stage1.task import Budgets
from stage2.prepare import run_extract, approve, load_approved, load_contracts, sha, parse_parts
from stage2.inventory import expand_selection
from stage2.bundled import run_pipeline
from stage2.bundle_reader import BundleReader
from stage2.context_cards import decode_writer_edges
from stage2.contracts import SECTIONS
from tests.test_stage2_inventory import selected


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.base=Path(self.tmp.name)
        self.root=self.base/'input';(self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text('int dep(int x);\nint f(int x) { return dep(x); }\n')
        (self.root/'lib/dep.c').write_text('int dep(int x) { return x + 1; }\n')
        self.manifest=expand_selection(self.root,selected(kind='module'))
        self.node=self.manifest['functions'][0];self.ident=self.node['id'];self.draft=self.base/'draft';self.ready=self.base/'ready'
        interface=self.base/'dep.c';interface.write_text('int dep(int x);\n/*@ Require x >= 0 Ensure result == x + 1 */\n')
        self.registry=[{'symbol':'dep','configuration':'always','declaration':{'path':'lib/code.c','start':1,'end':1},
                       'interface_file':'dep.c','sha256':sha(interface),'status':'reviewed','format':'qcp'}]
        self.registry_path=self.base/'contracts.json';self.registry_path.write_text(json.dumps(self.registry))
        self.budgets=Budgets(calls=20,seconds=20,context_chars=60000,reserve_seconds=0)
        self.roles=[]

    def extract(self,contracts=True):
        def factory(role,tid):
            self.roles.append(role);calls=[0]
            def model(messages,timeout):
                calls[0]+=1
                if calls[0]==1:return json.dumps({'tool':'read','path':'lib/code.c','start':1,'count':2})
                return json.dumps({'tool':'finish','report':{'function_id':self.ident,'snippets':[{'kind':'declaration','source':{'path':'lib/code.c','start':1,'end':1},'symbol':'dep','condition':'always','reason':'callee interface'}],
                    'calls':[{'symbol':'dep','target_id':None,'declaration_index':0,'callsite':self.node['source'],'condition':'always','unresolved':''}],
                    'macro_expansions':[],'coverage':{k:'checked' for k in ('types','macros','declarations')},'unknowns':[]}})
            return model
        return run_extract(self.root,self.draft,self.manifest,{'module':'fixture'},factory,
            contracts=load_contracts(self.registry_path) if contracts else [],budgets=self.budgets)

    def mark_review(self):
        p=self.draft/'preparation.json';d=json.loads(p.read_text());d['functions'][self.ident]['review']={
            'approved':True,'configuration':'fixture integer environment','changes':'Reviewed declaration and QCP contract; target unchanged.'}
        p.write_text(json.dumps(d));return d

    def seal(self):
        return approve(self.draft,self.ready,reviewer='fixture human',note='reviewed scope and dependencies')

    def model_factory(self,role,tid):
        self.roles.append(role)
        if role=='extract_source':raise AssertionError('spec phase must never extract')
        def model(messages,timeout):
            a=json.JSONDecoder().raw_decode(messages[0]['content'].split('任务：\n',1)[1])[0]
            artifacts={}
            for m in messages[1:]:
                try:d=json.loads(m['content'])
                except ValueError:continue
                if isinstance(d,dict) and d.get('kind')=='derived_interpretation_not_original_evidence':artifacts[d['id']]=d['content']
            node=a['function']
            if role=='write':
                self.assertIn('callee-contracts',artifacts)
                edges=decode_writer_edges(artifacts).values()
                r={'function_id':node['id'],'proof_status':'not_proved','sections':{k:'conditional fixture '+k for k in SECTIONS},
                   'claims':[{'id':'c','kind':'interpretation','text':'adapted input','evidence':[node['source']]}],
                   'reference_uses':[],'common_needs':[],'caller_scenarios':[],'unknowns':[],
                   'call_requirements':[{'edge_id':e['id'],'precondition':'x >= 0','postcondition':'result=x+1','status':'required_not_guaranteed','evidence':[e['callsite']]} for e in edges]}
            else:
                self.assertIn('callee-contracts',artifacts)
                r={'function_id':node['id'],'verdict':'pass','checks':{k:'checked' for k in a['checks']},'findings':[],'evidence':[],'material_requests':[]}
            return json.dumps({'tool':'finish','report':r})
        return model

    def test_single_file_extraction_then_review_and_spec_without_extractor(self):
        state=self.extract();self.assertEqual(self.roles,['extract_source'])
        self.assertEqual(state['status'],'awaiting_source_review')
        self.assertEqual(len(list(self.draft.glob('*.c'))),1)
        text=(self.draft/(self.ident+'.c')).read_text()
        self.assertIn('Ensure result',text);self.assertNotIn('int dep(int x) {',text)
        self.assertFalse(list(self.draft.glob('functions/*/candidate.json')))
        self.mark_review();approved=self.seal();self.assertEqual(len(list(self.ready.glob('*.c'))),1)
        self.roles=[]
        result=run_pipeline(self.root,self.base/'spec',self.manifest,{'module':'fixture'},self.model_factory,
                            budgets=self.budgets,prepared_source=self.ready,max_revisions=0)
        self.assertEqual(result['status'],'candidates_reviewed',result)
        self.assertNotIn('extract_source',self.roles)
        from stage4.pipeline import load_upstream
        graph,nodes,_=load_upstream(self.root,self.base/'spec')
        self.assertTrue(nodes[self.ident]['source']['path'].startswith('prepared/'))
        bundle=approved['functions'][self.ident]['bundle']
        reader=BundleReader(self.root,self.base/'reads',bundles=[(self.ready,bundle)])
        result=reader.execute({'tool':'read',**{'path':nodes[self.ident]['source']['path'],'start':1,'count':1}})
        self.assertEqual(result['source'],'reviewed_adapted_input_not_original')

    def test_source_request_never_starts_reextraction(self):
        self.extract();self.mark_review();self.seal();self.roles=[]
        def factory(role,tid):
            model=self.model_factory(role,tid)
            def call(messages,timeout):
                action=json.loads(model(messages,timeout))
                if role=='write':action['report']['material_requests']=[{'symbol':'dep','question':'interface conflict','reason':'return to source review'}]
                return json.dumps(action)
            return call
        result=run_pipeline(self.root,self.base/'spec',self.manifest,{'module':'fixture'},factory,
                            budgets=self.budgets,prepared_source=self.ready,max_revisions=3)
        self.assertEqual(result['status'],'incomplete')
        self.assertEqual(self.roles,['write'])
        self.assertTrue((self.base/'spec/functions'/self.ident/'source_revision_request.json').exists())

    def test_current_api_requires_preparation(self):
        with self.assertRaisesRegex(ValueError,'independent source preparation'):
            run_pipeline(self.root,self.base/'spec',self.manifest,{},lambda *args:None)

    def test_callee_body_inserted_during_review_rejected(self):
        self.extract();p=self.draft/(self.ident+'.c');p.write_text(p.read_text()+'\nint dep(int x) { return x; }\n')
        self.mark_review()
        with self.assertRaisesRegex(ValueError,'exactly the target'):self.seal()

    def test_review_required_and_missing_contract_stops(self):
        self.extract(contracts=False)
        with self.assertRaisesRegex(ValueError,'explicit per-function review'):self.seal()
        self.mark_review()
        with self.assertRaisesRegex(ValueError,'processed callee specification'):self.seal()
        self.assertFalse(self.ready.exists())

    def test_edits_recalculate_lines_and_do_not_change_original(self):
        self.extract();path=self.draft/(self.ident+'.c');path.write_text(path.read_text().replace('return dep(x);','\n    return dep(x);\n'))
        self.mark_review();d=self.seal();node=d['functions'][self.ident]['node']
        self.assertGreater(node['source']['end']-node['source']['start'],0)
        self.assertEqual((self.root/'lib/code.c').read_text(),'int dep(int x);\nint f(int x) { return dep(x); }\n')
        self.assertNotEqual(sha(path),d['functions'][self.ident]['bundle']['provenance']['initial_sha256'])

    def test_new_unlisted_call_requires_review_metadata(self):
        self.extract();p=self.draft/(self.ident+'.c');p.write_text(p.read_text().replace('return dep(x);','return dep(other(x));'))
        self.mark_review()
        with self.assertRaisesRegex(ValueError,'unrecorded calls'):self.seal()

    def test_contract_body_and_hash_rejected(self):
        (self.base/'dep.c').write_text('int dep(int x) { return x; }')
        with self.assertRaisesRegex(ValueError,'hash changed'):load_contracts(self.registry_path)
        self.registry[0]['sha256']=sha(self.base/'dep.c');self.registry_path.write_text(json.dumps(self.registry))
        with self.assertRaisesRegex(ValueError,'not a function implementation'):load_contracts(self.registry_path)

    def test_approved_changes_rejected(self):
        self.extract();self.mark_review();self.seal()
        p=self.ready/(self.ident+'.c');p.write_text(p.read_text()+'/* later edit */')
        from stage1.runner import snapshot
        with self.assertRaisesRegex(ValueError,'bundle changed'):load_approved(self.ready,self.manifest,snapshot(self.root))

    def test_preparation_path_escape_and_markers_rejected(self):
        self.extract();d=self.mark_review();d['functions'][self.ident]['file']='../dep.c';(self.draft/'preparation.json').write_text(json.dumps(d))
        with self.assertRaisesRegex(ValueError,'invalid relative'):self.seal()
        with self.assertRaisesRegex(ValueError,'missing/unfinished'):parse_parts('int f(void) {}')

    def test_contract_configuration_is_not_guessed_from_symbol(self):
        self.registry[0]['configuration']='different-build'
        self.registry_path.write_text(json.dumps(self.registry))
        result=self.extract()
        self.assertTrue(result['functions'][self.ident]['interface_gaps'])
        self.mark_review()
        with self.assertRaisesRegex(ValueError,'processed callee specification'):self.seal()

    def test_approval_cannot_write_into_original_input(self):
        self.extract();self.mark_review()
        with self.assertRaisesRegex(ValueError,'outside original input'):
            approve(self.draft,self.root/'approved',reviewer='fixture',note='review')
        self.assertFalse((self.root/'approved').exists())

    def test_reviewed_macro_expansion_remains_in_single_file(self):
        self.extract();d=self.mark_review();entry=d['functions'][self.ident]
        p=self.draft/entry['file'];text=p.read_text()
        text=text.replace('/* preparation:begin implementation */',
            '/* preparation:begin snippet-1 */\n#define STEP(x) dep(x)\n/* preparation:end snippet-1 */\n/* preparation:begin implementation */')
        text=text.replace('return dep(x);','return STEP(x);');p.write_text(text)
        report=entry['report'];report['snippets'].append({'kind':'macro','symbol':'STEP','condition':'always','reason':'human adaptation',
            'part':'snippet-1','source':{'path':'human-added','start':1,'end':1}})
        report['calls'][0].update(symbol='STEP',declaration_index=1)
        report['macro_expansions']=[{'symbol':'dep','declaration_index':0,'target_id':None,'condition':'always','unresolved':'',
             'root_call_index':0,'parent_expansion_index':None,'macro_index':1,'callsite':{}}]
        (self.draft/'preparation.json').write_text(json.dumps(d))
        result=self.seal();bundle=result['functions'][self.ident]['bundle']
        self.assertEqual(len(bundle['files']),1)
        self.assertEqual(bundle['macro_units'][0]['symbol'],'STEP')
        self.assertEqual(bundle['report']['callee_contracts'][0]['symbol'],'dep')

    def test_original_input_changes_require_new_preparation(self):
        self.extract();self.mark_review()
        (self.root/'lib/code.c').write_text('int changed;')
        with self.assertRaisesRegex(ValueError,'input changed'):self.seal()

    def test_cli_requires_separate_preparation_before_model(self):
        from stage2.legacy_cli import main
        argv=['stage2','--manifest','fixture','--output',str(self.base/'spec')]
        with patch('sys.stderr'),patch('sys.argv',argv),patch('stage2.legacy_cli.load_manifest',return_value=(self.manifest,{})),patch('stage1.codex_backend.CodexModel') as model:
            with self.assertRaises(SystemExit):main()
            model.assert_not_called()
