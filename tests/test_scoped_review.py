import copy
import json
import unittest
from stage2.review_flow import jobs, validate
from stage2.required_inputs import plan
from stage2.bundled import requests
from tests import test_bundled_pipeline as fixtures
Harness=fixtures.Harness


class ScopedReviewTests(unittest.TestCase):
    setUp=fixtures.BundledPipelineTests.setUp
    run_fixture=fixtures.BundledPipelineTests.run_fixture
    def test_quality_and_calls_have_separate_inputs(self):
        status,graph,h=self.run_fixture()
        reviews=[e for e in h.events if e['role']=='review']
        quality=next(e for e in reviews if e['assignment'].get('review_scope')=='quality')
        self.assertEqual(quality['assignment']['edges'],[])
        calls=next(e for e in reviews if e['assignment'].get('review_scope','').startswith('calls-'))
        self.assertLessEqual(len(calls['assignment']['edges']),4)
        self.assertFalse(any(k.startswith('material:') for k in calls['artifacts']))
        self.assertEqual(status['status'],'candidates_reviewed')

    def test_one_scoped_failure_cannot_pass_aggregate(self):
        h=Harness(self.manifest,fail=lambda r,s,t:r=='review' and s=='a' and t.endswith('-behavior'))
        status,graph,_=self.run_fixture(h)
        self.assertNotEqual(graph['nodes'][h.by_symbol['a']['id']]['status'],'reviewed_candidate')
        self.assertEqual(status['status'],'incomplete')
        self.assertTrue(list(self.output.glob('tasks/*/completed-checks.json')))

    def test_material_preflight_skips_model_review(self):
        status,graph,h=self.run_fixture(Harness(self.manifest,request=True),max_revisions=0)
        self.assertFalse(any(e['role']=='review' and e['symbol']=='unrelated' for e in h.events))
        self.assertEqual(status['status'],'incomplete')

    def test_all_incident_edges_assigned_once(self):
        _,graph,h=self.run_fixture()
        node=graph['nodes'][h.by_symbol['a']['id']]
        base=next(iter(graph['edges'].values()))
        graph['edges']={str(i):{**base,'id':str(i)} for i in range(13)}
        scheduled=jobs(node,node['spec'],graph,{},[])
        assigned=[e['id'] for _,a,_,_,_ in scheduled for e in a['edges']]
        self.assertEqual(sorted(assigned),sorted(graph['edges']))
        self.assertEqual(len(assigned),len(set(assigned)))


class ReviewContractTests(unittest.TestCase):
    def test_requests_not_arbitrarily_capped_at_eight(self):
        self.assertEqual(requests({'material_requests':[{'symbol':'x','question':'q','reason':'r'}]*10}),[])
        self.assertTrue(requests({'material_requests':[{'symbol':'x'}]}))

    def test_macro_read_keeps_guard_lines(self):
        node={'id':'f','source':{'path':'f.c','start':1,'end':2},'materials':[]}
        graph={'nodes':{'f':{**node,'spec':None}},'edges':{},'discoveries':{}}
        # Use a minimal valid graph produced by new_graph for its context defaults.
        from stage2.graph import new_graph
        graph=new_graph({'functions':[{**node,'symbol':'f','configuration':'c'}]})
        source={'path':'h.h','start':186,'end':198}
        actions=plan(node,graph,{},bundles=[(None,{'report':{'snippets':[{'kind':'macro','source':source}]}})])
        macro=next(x for x in actions if x.get('path')=='h.h')
        self.assertEqual((macro['start'],macro['count']),(186,13))

    def test_mismatch_requires_concrete_scenario(self):
        report={'function_id':'f','verdict':'needs_revision','checks':{'call_requirements':'checked'},
                'findings':[{'description':'wrong result','blocking':True}],'evidence':[]}
        errors=validate(report,None,set(),ident='f',keys=['call_requirements'],required_artifacts=[],evidence=[])
        self.assertTrue(any('concrete input' in x for x in errors))
        report['findings'][0].update(input='x=0',actual='returns 1',required='returns 0')
        self.assertEqual(validate(report,None,set(),ident='f',keys=['call_requirements'],required_artifacts=[],evidence=[]),[])
