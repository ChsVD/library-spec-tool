import copy
import unittest
from stage4 import contracts
from stage4.pipeline import render
from tests import test_stage3 as fixtures


class UpstreamConditionsTests(unittest.TestCase):
    setUp=fixtures.Stage3Tests.setUp
    tearDown=fixtures.Stage3Tests.tearDown

    def prepare(self):
        self.nodes[self.ids[0]]['spec']['conditional_assumptions']=[{
            'id':'alloc-failure','condition':'Allocator failure preserves the old live allocation.'}]
        report=fixtures.proposal(self.ids)
        report['upstream_conditions']=contracts.upstream_conditions(self.nodes)
        return report

    def validate(self,report):
        return contracts.candidate(report,self.reader,self.reads,nodes=self.nodes,extracts=self.extracts)

    def test_scope_cannot_be_dropped_or_changed(self):
        report=self.prepare()
        self.assertEqual(self.validate(report),[])
        self.assertIn('alloc-failure',render(report))
        del report['upstream_conditions']
        self.assertTrue(self.validate(report))
        report=self.prepare()
        report['upstream_conditions'][self.ids[0]][0]['condition']='allocation always succeeds'
        self.assertTrue(self.validate(report))

    def test_review_must_assess_each_condition_without_promoting_it(self):
        proposal=self.prepare(); review=fixtures.review()
        def validate():
            return contracts.review(review,self.reader,self.reads|{'candidate'},proposal=proposal,nodes=self.nodes)
        self.assertTrue(validate())
        review['upstream_condition_checks']=[{'function_id':self.ids[0],'assumption_id':'alloc-failure',
            'decision':'preserved','explanation':'Candidate retains condition; no lemma claims the allocator guarantee is proved.'}]
        self.assertEqual(validate(),[])
        review['upstream_condition_checks'][0]['decision']='unknown'
        self.assertTrue(validate())
        review['verdict']='insufficient'
        self.assertEqual(validate(),[])

    def test_duplicate_or_unknown_review_checks_rejected(self):
        proposal=self.prepare(); review=fixtures.review()
        item={'function_id':self.ids[0],'assumption_id':'alloc-failure','decision':'preserved','explanation':'retained'}
        review['upstream_condition_checks']=[item,copy.deepcopy(item)]
        self.assertTrue(contracts.review(review,self.reader,self.reads|{'candidate'},proposal=proposal,nodes=self.nodes))
        review['upstream_condition_checks']=[{**item,'assumption_id':'other'}]
        self.assertTrue(contracts.review(review,self.reader,self.reads|{'candidate'},proposal=proposal,nodes=self.nodes))
