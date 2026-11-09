"""Dependency-first orchestration tests. Synthetic responses are not semantic validation."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from stage1.task import Budgets
from stage1.report import SECTIONS
from stage1.reader import Reader
from stage1.focused_contracts import dependency_frontier, validate_graph_plan, validate_selection, validate_screening
from stage1.multi import run_pipeline

class FocusedTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(); self.base=Path(self.temp.name); self.root=self.base/'input'
        for lib in ['openssl','sm2','mini-gmp']:
            (self.root/lib).mkdir(parents=True); (self.root/lib/'sample.c').write_text('fixture first line\nfixture second line\n')
        self.reader=Reader(self.root,self.base/'read.jsonl')
        for lib in ['openssl','sm2','mini-gmp']: self.reader.execute({'tool':'read','path':lib+'/sample.c'})
        self.plan={'coverage':{lib:{'mapped_areas':'fixture','unread_areas':'fixture','configuration_unknowns':'fixture'} for lib in ['openssl','sm2','mini-gmp']},'evidence':[self.cite(lib) for lib in ['openssl','sm2','mini-gmp']], 'modules':[]}
        for ident,lib in [('base','openssl'),('consumer','openssl'),('match','sm2'),('unrelated','mini-gmp'),('uncertain','sm2')]:
            self.plan['modules'].append({'id':ident,'library':lib,'title':ident,'scope':[lib+'/sample.c'],'questions':'fixture questions','responsibilities':'fixture role','boundary':'fixture boundary','dependency_status':'checked','dependency_notes':'fixture dependency inspection','dependencies':[],'evidence':[self.cite(lib)]})
        self.plan['modules'][1]['dependencies']=[self.edge('base')]
    def tearDown(self): self.temp.cleanup()
    def cite(self,lib): return {'path':lib+'/sample.c','start':1,'end':2}
    def edge(self,dest,kind='call',certainty='confirmed'):
        return {'prerequisite':dest,'external':'outside' if dest is None else '', 'kind':kind,'certainty':certainty,'reason':'fixture requirement','evidence':[self.cite('openssl')]}
    def factory(self, *, match=True, change_dependency=False, review_pass=True, reject_pair=False, fail_module=False, sneak=False, omit_screen=False, unread_pair=False, switch_target=False, unread_review=False, mutate=False, unable=False):
        created=[]; artifacts_seen={}
        def build(role,ident):
            created.append((role,ident))
            cite=self.cite
            selected='base'
            selection={'status':'proposed','primary':selected,'rationale':'fixture dependency ordering','scope':'fixture scope','blockers':'fixture unknowns','evidence':[cite('openssl')]}
            screening={'target':'base','candidates':[{'reference':'match','decision':'match' if match else 'no_match','reason':'fixture boundary'}, {'reference':'unrelated','decision':'no_match','reason':'unrelated boundary'}, {'reference':'uncertain','decision':'unknown','reason':'missing boundary detail'}]}
            actions=[]
            def reads(libs): return [{'tool':'read','path':lib+'/sample.c'} for lib in libs]
            def artifact(ids): return [{'tool':'artifact','id':i} for i in ids]
            if role=='planner': report=copy.deepcopy(self.plan); actions=reads(['openssl','sm2','mini-gmp'])
            elif role=='selection':
                report={**selection,'status':'unable','primary':None} if unable else selection
                actions=artifact(['plan','dependency_frontier'])+reads(['openssl'])
            elif role=='screening':
                report=screening
                if omit_screen: report['candidates']=report['candidates'][:-1]
                actions=artifact(['card:base','card:match','card:unrelated','card:uncertain'])
                if sneak: actions.insert(0,{'tool':'read','path':'sm2/sample.c'})
            elif role=='module':
                mid=ident.removeprefix('module-'); m=next(m for m in self.plan['modules'] if m['id']==mid)
                report={'id':mid,'library':m['library'],'title':mid,'depth':'detailed','sections':{s:'Fixture only' for s in SECTIONS},'evidence':[cite(m['library'])], 'dependency_check':{'status':'conflict' if change_dependency and mid=='base' else 'confirmed','notes':'fixture dependency check'}}
                actions=reads([m['library']])
            elif role=='comparison':
                report={'id':'pair-match','target':'consumer' if switch_target else 'base','reference':'match','relation':'none' if reject_pair else 'candidate','evidence':[cite('openssl'),cite('sm2')], **{s:'Fixture detail' for s in ['basis','differences','unknowns','representation','preconditions','dependencies','proof_status','adaptation']}}
                actions=artifact(['selection','screening','module:base','module:match'])+reads(['openssl'] if unread_pair else ['openssl','sm2'])
            elif role=='review':
                mids=['base','match'] if match else ['base']
                report={'verdict':'pass' if review_pass else 'needs_revision','coverage_checked':mids,'findings':[],'evidence':[cite(lib) for lib in (['openssl','sm2'] if match else ['openssl'])]}
                actions=artifact(['plan','dependency_frontier','selection','screening']+['module:'+m for m in mids]+(['comparison:pair-match'] if match else []))+reads(['openssl'] if unread_review else (['openssl','sm2'] if match else ['openssl']))
            else: raise AssertionError(role)
            actions.append({'tool':'finish','report':report})
            for a in actions: a['draft']='Synthetic finding; not real library analysis'
            iterator=iter(actions)
            def model(messages,timeout):
                artifacts_seen[ident]=messages[0]['content']
                if fail_module and ident=='module-match': raise RuntimeError('fixture module failure')
                action=next(iterator,{'tool':'finish','report':report})
                if mutate and role=='review' and action['tool']=='finish': (self.root/'changed').write_text('changed')
                return json.dumps(action)
            return model
        return build,created,artifacts_seen
    def run_fixture(self,**opts):
        factory,created,seen=self.factory(**opts)
        result=run_pipeline(self.root,self.base/'out',factory,budgets=Budgets(seconds=60,reserve_seconds=0,validation_retries=0),concurrency=2)
        return result,created,seen
    def test_graph_direction_and_frontier(self):
        self.assertEqual(validate_graph_plan(self.plan,self.reader,set()),[])
        graph=dependency_frontier(self.plan)
        self.assertEqual(graph['eligible'],['base']); self.assertEqual(graph['dependent_counts']['base'],1)
        self.assertIn('consumer',graph['blocked'])
    def test_cycles_unknown_and_external_are_blocking(self):
        self.plan['modules'][0]['dependencies']=[self.edge('consumer')]
        graph=dependency_frontier(self.plan)
        self.assertEqual(graph['eligible'],[]); self.assertEqual(graph['cycles'],[['base','consumer']])
        self.plan['modules'][0]['dependencies']=[self.edge(None)]
        self.assertEqual(dependency_frontier(self.plan)['eligible'],[])
        self.plan['modules'][0]['dependencies']=[]; self.plan['modules'][0]['dependency_status']='unknown'
        self.assertEqual(dependency_frontier(self.plan)['eligible'],[])
    def test_build_relation_does_not_set_proof_order_but_unknown_blocks(self):
        self.plan['modules'][0]['dependencies']=[self.edge('consumer','build')]
        self.assertEqual(dependency_frontier(self.plan)['eligible'],['base'])
        self.plan['modules'][0]['dependencies'][0]['certainty']='unknown'
        self.assertEqual(dependency_frontier(self.plan)['eligible'],[])
    def test_invalid_endpoint_cross_library_and_unread_graph_evidence(self):
        for dest in ['missing','match']:
            self.plan['modules'][1]['dependencies']=[self.edge(dest)]
            self.assertTrue(validate_graph_plan(self.plan,self.reader,set()))
        self.plan['modules'][1]['dependencies']=[self.edge('base')]
        self.reader.reads={}
        self.assertTrue(validate_graph_plan(self.plan,self.reader,set()))
    def test_selection_cannot_skip_prerequisite(self):
        report={'status':'proposed','primary':'consumer','rationale':'fixture','scope':'fixture','blockers':'fixture','evidence':[self.cite('openssl')]}
        errors=validate_selection(report,self.reader,{'plan','dependency_frontier'},plan=self.plan,frontier=dependency_frontier(self.plan))
        self.assertTrue(any('frontier' in e for e in errors))
    def test_default_pipeline_selects_before_screening_and_only_deep_reads_matches(self):
        result,created,seen=self.run_fixture()
        self.assertEqual(result['status'],'fixture_pipeline_complete',result)
        self.assertFalse(result['user_approved']); self.assertEqual(result['selected_module'],'base')
        roles=[r for r,_ in created]
        self.assertLess(roles.index('selection'),roles.index('screening')); self.assertLess(roles.index('screening'),roles.index('module'))
        self.assertNotIn('aggregate',roles)
        self.assertEqual(set(result['completed_modules']),{'base','match'})
        self.assertNotIn('module:unrelated',seen['comparison-match'])
        self.assertNotIn('module:uncertain',seen['comparison-match'])
        for name in ['dependency_graph.md','selection.md','screening.md','modules/base.md','comparisons/match.md','reviews/review-match.md','final/report.md']:
            self.assertTrue((self.base/'out'/name).exists(),name)
    def test_no_supported_frontier_stops_with_selection_and_graph(self):
        self.plan['modules'][0]['dependency_status']='unknown'
        result,created,_=self.run_fixture(unable=True)
        self.assertEqual(result['reason'],'no_supported_target')
        self.assertFalse(any(r=='screening' for r,_ in created))
        self.assertTrue((self.base/'out/selection.md').exists())
        self.assertTrue((self.base/'out/dependency_graph.json').exists())

    def test_screening_is_enforced_card_only(self):
        result,_,_=self.run_fixture(sneak=True)
        self.assertEqual(result['status'],'fixture_pipeline_complete')
        self.assertFalse((self.base/'out/tasks/screening/reads.jsonl').exists())
        self.assertIn('Tool disabled',(self.base/'out/tasks/screening/conversation.jsonl').read_text())
    def test_missing_reference_screening_blocks_deep_read(self):
        result,created,_=self.run_fixture(omit_screen=True)
        self.assertNotEqual(result['status'],'fixture_pipeline_complete'); self.assertFalse(any(r=='module' for r,_ in created))
    def test_no_match_preserves_target_and_skips_comparator(self):
        result,created,_=self.run_fixture(match=False)
        self.assertEqual(result['status'],'fixture_pipeline_complete',result)
        self.assertEqual(result['completed_modules'],['base']); self.assertFalse(any(r=='comparison' for r,_ in created))
        final=json.loads((self.base/'out/final/report.json').read_text())
        self.assertEqual(final['comparisons'],[]); self.assertTrue(final['unresolved_screening'])
    def test_new_target_dependency_stops_before_comparison(self):
        result,created,_=self.run_fixture(change_dependency=True)
        self.assertEqual(result['reason'],'target_dependencies_need_replanning')
        self.assertFalse(any(r=='comparison' for r,_ in created)); self.assertTrue((self.base/'out/selection.json').exists())
    def test_pair_requires_bilateral_original_evidence(self):
        result,created,_=self.run_fixture(unread_pair=True)
        self.assertNotEqual(result['status'],'fixture_pipeline_complete'); self.assertFalse(any(r=='review' for r,_ in created))
    def test_pair_cannot_switch_target(self):
        result,_,_=self.run_fixture(switch_target=True)
        self.assertNotEqual(result['status'],'fixture_pipeline_complete')
    def test_deep_comparison_can_reject_initial_match(self):
        result,_,_=self.run_fixture(reject_pair=True)
        self.assertEqual(result['status'],'fixture_pipeline_complete')
        self.assertEqual(json.loads((self.base/'out/comparisons/match.json').read_text())['relation'],'none')
    def test_review_failure_or_unread_evidence_blocks_final(self):
        result,_,_=self.run_fixture(unread_review=True)
        self.assertNotEqual(result['status'],'fixture_pipeline_complete'); self.assertFalse((self.base/'out/final').exists())
    def test_review_can_request_revision(self):
        result,_,_=self.run_fixture(review_pass=False)
        self.assertEqual(result['status'],'needs_revision'); self.assertFalse((self.base/'out/final').exists())
    def test_partial_worker_failure_preserves_selection_and_completed_report(self):
        result,_,_=self.run_fixture(fail_module=True)
        self.assertEqual(result['reason'],'module_tasks_incomplete')
        self.assertTrue((self.base/'out/selection.json').exists()); self.assertTrue((self.base/'out/modules/base.json').exists())
    def test_input_mutation_blocks_final(self):
        result,_,_=self.run_fixture(mutate=True)
        self.assertEqual(result['status'],'input_changed'); self.assertFalse((self.base/'out/final').exists())

if __name__=='__main__': unittest.main()
