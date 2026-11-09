from stage3.scenario_guidance import load_catalog, PROMPT as SCENARIO_PROMPT
from tests.scenario_fixture import scenario
import json
import tempfile
import unittest
from pathlib import Path
from stage2.inventory import expand_selection
from stage3.reference import PROMPT,build_graph,run as run_reference,validate
from functools import partial
build_graph=partial(build_graph,graph_backend="lexical")
# These tests retain the explicit unreviewed workflow.
run=partial(run_reference,review=False,graph_backend="lexical")

class ReferenceTests(unittest.TestCase):
    def setup_input(self,text):
        t=tempfile.TemporaryDirectory();self.addCleanup(t.cleanup);base=Path(t.name);root=base/'input';root.mkdir();(root/'a.c').write_text(text)
        manifest={'version':2,'scope_decision':'all functions','materials':{},'selection':{'id':'m','module_id':'m','kind':'module','paths':['.'],'configuration':'unknown','materials':[]}}
        return root,base/'out',expand_selection(root,manifest)
    def factory(self,captured):
        def make(ident):
            def model(messages,timeout):
                a=json.loads(messages[1]['content']);captured.append(a)
                return json.dumps({'tool':'finish','report':{'functions':[{'function_id':n['id'],'scenario_analysis':scenario(a),'observations':'Observed source','suggested_spec':'Conditional suggested behavior','assumptions':'Unverified','callee_requirements':[{'callee':'leaf','requirement':'Return a value'}]} for n in a['assigned']]}})
            return model
        return make
    def test_scc_cycle_and_caller_first(self):
        root,out,m=self.setup_input('int leaf(void){return 1;}\nint a(void){return b()+leaf();}\nint b(void){return a();}\nint top(void){return a();}')
        g=build_graph(root,m);groups=[[g['nodes'][i]['symbol'] for i in c['members']] for c in g['components']]
        self.assertEqual(groups[0],['top']);self.assertEqual(set(groups[1]),{'a','b'});self.assertEqual(groups[2],['leaf'])
    def test_generation_without_callee_contract_or_extraction(self):
        root,out,m=self.setup_input('int leaf(void){return MISSING(1);}\nint top(void){return leaf();}')
        captured=[];g=run(root,out,m,{'target-module':'Module explanation'},self.factory(captured))
        self.assertTrue(all(n['status']=='reference_draft' for n in g['nodes'].values()))
        self.assertEqual(captured[0]['assigned'][0]['symbol'],'top')
        self.assertTrue(captured[1]['incoming'][0]['requirements'])
        self.assertTrue(captured[1]['neighbor_drafts'][0]['spec'])
        self.assertEqual(len(list((out/'specs').glob('*.md'))),2)
        self.assertTrue(g['unknown_calls']);self.assertFalse((out/'prepared.json').exists())
    def test_resume_only_pending(self):
        root,out,m=self.setup_input('int leaf(void){return 1;} int top(void){return leaf();}')
        captured=[];run(root,out,m,{},self.factory(captured),max_components=1)
        self.assertEqual(len(captured),1)
        g=run(root,out,m,{},self.factory(captured),resume=True)
        self.assertEqual(len(captured),2);self.assertTrue(all(n['spec'] for n in g['nodes'].values()))
    def test_large_scc_splits_without_dropping_members(self):
        root,out,m=self.setup_input('int a(void){'+('x++;\n'*1000)+'return b();} int b(void){'+('x++;\n'*1000)+'return a();}')
        # Keep the assignment budget independent of template wording/length.
        captured=[];g=run(root,out,m,{},self.factory(captured),max_chars=len(PROMPT)+len(SCENARIO_PROMPT)+len(json.dumps(load_catalog(),ensure_ascii=False))+17000)
        self.assertEqual(len(captured),2);self.assertEqual(captured[0]['component'],captured[1]['component'])
        self.assertTrue(all(n['spec'] for n in g['nodes'].values()))
    def test_oversize_saved_not_silently_truncated(self):
        root,out,m=self.setup_input('int a(void){'+('x++;'*3000)+'return 1;}')
        captured=[];g=run(root,out,m,{},self.factory(captured),max_chars=10000)
        self.assertFalse(captured);self.assertEqual(next(iter(g['nodes'].values()))['status'],'context_too_large')
        self.assertTrue(list((out/'tasks').rglob('assignment.json')))
    def test_invalid_response_saved_and_repaired_once(self):
        root,out,m=self.setup_input('int a(void){return 1;}');calls=[]
        good=self.factory(calls)('scc')
        def model(messages,timeout):
            if len(messages)==2:return '{bad'
            return good(messages,timeout)
        g=run(root,out,m,{},lambda ident:model)
        self.assertEqual(next(iter(g['nodes'].values()))['status'],'reference_draft')
        self.assertTrue(list((out/'tasks').rglob('response-0.txt')))
    def test_duplicate_coverage_rejected(self):
        with self.assertRaises(ValueError):validate({'functions':[{'function_id':'a'},{'function_id':'a'}]},['a','b'])
    def test_prepare_only_no_model_and_stale_resume(self):
        root,out,m=self.setup_input('int a(void){return 1;}');run(root,out,m,{},prepare_only=True)
        self.assertEqual(json.loads((out/'status.json').read_text())['status'],'planned')
        (root/'a.c').write_text('int a(void){return 2;}')
        with self.assertRaises(ValueError):run(root,out,m,{},self.factory([]),resume=True)
    def test_cross_file_static_not_bound(self):
        root,out,m=self.setup_input('int a(void){return hidden();}')
        (root/'b.c').write_text('static int hidden(void){return 1;}')
        original={'version':2,'scope_decision':'all','materials':{},'selection':m['selection_inventory']['selection']}
        g=build_graph(root,expand_selection(root,original))
        self.assertFalse(g['edges']);self.assertTrue(g['unknown_calls'])

    def test_unlimited_context_keeps_large_scc_and_response(self):
        root,out,m=self.setup_input('int a(void){'+('x++;'*9000)+'return b();} int b(void){'+('x++;'*9000)+'return a();}')
        captured=[];factory=self.factory(captured)
        def make(ident):
            base=factory(ident)
            def model(messages,timeout):
                response=json.loads(base(messages,timeout))
                for r in response['report']['functions']:r['suggested_spec']='reference '*9000
                return json.dumps(response)
            return model
        g=run(root,out,m,{},make,max_chars=None)
        self.assertEqual(len(captured),1)
        self.assertEqual(len(captured[0]['assigned']),2)
        self.assertTrue(all(n['status']=='reference_draft' for n in g['nodes'].values()))
        self.assertIsNone(json.loads((out/'identity.json').read_text())['max_chars'])

    def test_callee_first_and_continuation_closure(self):
        root,out,m=self.setup_input('int leaf(void){return 1;} int mid(void){return leaf();} int top(void){return mid();} int unrelated(void){return 0;}')
        seed=dict(m);seed['functions']=[n for n in m['functions'] if n['symbol']=='top']
        captured=[];run(root,out,seed,{},self.factory(captured))
        more=out.parent/'continued';captured=[]
        g=run(root,more,m,{},self.factory(captured),order='callee-first',continue_from=out)
        self.assertEqual([a['assigned'][0]['symbol'] for a in captured],['leaf','mid'])
        self.assertEqual({n['symbol'] for n in g['nodes'].values()},{'top','mid','leaf'})
        top=next(n for n in g['nodes'].values() if n['symbol']=='top');self.assertTrue(top['inherited'])
        self.assertTrue(all(n['spec'] for n in g['nodes'].values()))

    def test_regenerate_top_down_transmits_fresh_demands(self):
        root,out,m=self.setup_input('int leaf(void){return 1;} int mid(void){return leaf();} int top(void){return mid();}')
        seed=dict(m);seed['functions']=[n for n in m['functions'] if n['symbol']=='top']
        run(root,out,seed,{},self.factory([]))
        captured=[]
        def factory(ident):
            base=self.factory(captured)(ident)
            def model(messages,timeout):
                r=json.loads(base(messages,timeout));a=json.loads(messages[1]['content'])
                for spec in r['report']['functions']:
                    spec['callee_requirements']=[{'callee':e['symbol'],'requirement':'fresh demand'} for e in a['outgoing'] if e['caller']==spec['function_id']]
                return json.dumps(r)
            return model
        g=run(root,out.parent/'new',m,{},factory,continue_from=out,regenerate=True,order='caller-first')
        self.assertEqual([a['assigned'][0]['symbol'] for a in captured],['top','mid','leaf'])
        for a in captured[1:]:self.assertEqual(a['incoming'][0]['requirements'][0]['requirement'],'fresh demand')
        self.assertFalse(any(n.get('inherited') for n in g['nodes'].values()))

    def test_repeated_calls_preserve_original_windows(self):
        root,out,m=self.setup_input('int leaf(void){return 1;}\nint top(void){\nint c=leaf();\nreturn leaf()+c;\n}')
        g=build_graph(root,m);e=next(iter(g['edges'].values()))
        self.assertEqual(len(e['callsites']),2)
        self.assertIn('int c=leaf();',e['callsites'][0]['code'])
        self.assertEqual(e['callsites'][0]['source']['path'],'a.c')

    def test_branch_scope_all_direct_callers_and_no_unrelated(self):
        from stage2.branch_scope import select as select_backend
        select=partial(select_backend,graph_backend="lexical")
        root,out,m=self.setup_input('int target(void){return 0;}\nint mid(void){return target();}\nint top(void){return mid();}\nint other(void){return target();}\nint unrelated(void){return 1;}')
        chosen=select(root,m,'target',['top'])
        self.assertEqual({n['symbol'] for n in chosen['functions']},{'target','mid','top','other'})
        self.assertEqual(len(chosen['branch_scope']['supplemental_root_ids']),1)
        with self.assertRaises(ValueError):select(root,m,'target',['unrelated'])

    def test_failed_parent_does_not_generate_child_without_demand(self):
        root,out,m=self.setup_input('int leaf(void){return 1;} int top(void){return leaf();}')
        calls=[]
        def factory(ident):
            def model(messages,timeout):
                calls.append(ident);raise RuntimeError('backend unavailable')
            return model
        g=run(root,out,m,{},factory,order='caller-first')
        self.assertEqual(len(calls),1)
        by={n['symbol']:n for n in g['nodes'].values()}
        self.assertEqual(by['top']['status'],'generation_failed')
        self.assertEqual(by['leaf']['status'],'upstream_incomplete')
