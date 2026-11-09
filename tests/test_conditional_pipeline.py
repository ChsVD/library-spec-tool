import json
import unittest
from tests import test_bundled_pipeline as fixtures


class ConditionalPipelineTests(unittest.TestCase):
    setUp=fixtures.BundledPipelineTests.setUp
    run_fixture=fixtures.BundledPipelineTests.run_fixture

    def test_conditional_candidate_survives_local_and_group_review(self):
        harness=fixtures.Harness(self.manifest)
        original=harness.factory
        def factory(role,tid):
            model=original(role,tid)
            def call(messages,timeout):
                action=json.loads(model(messages,timeout))
                if action.get('tool')=='finish' and model.node['symbol']=='a':
                    report=action['report']
                    if role=='extract_source':
                        report['unknowns']=[{'description':'Missing b behavior guarantee','blocking':True,
                                             'category':'dependency_contract','symbol':'b'}]
                    elif role=='write':
                        condition='Assume b returns its argument.'
                        report['sections']['environment']=condition
                        report['conditional_assumptions']=[{'id':'b-result','symbol':'b','condition':condition,
                            'affected_claim_ids':['meaning'],'explanation':'This wrapper requires the dependency result.',
                            'gaps':[{'source':'extraction_unknowns','index':0}]}]
                    elif role=='review':
                        report['assumption_checks']=[{'id':'b-result','decision':'acceptable_condition',
                            'explanation':'Scope is explicit; dependency guarantee remains unproved.'}]
                return json.dumps(action)
            return call
        harness.factory=factory
        status,graph,_=self.run_fixture(harness,max_revisions=0)
        self.assertEqual(status['status'],'candidates_reviewed',status)
        node=graph['nodes'][harness.by_symbol['a']['id']]
        self.assertEqual(node['review']['acceptance_scope'],'conditional_candidate_not_proved')
        self.assertEqual(node['review']['conditional_assumptions'],node['spec']['conditional_assumptions'])
        self.assertTrue(graph['discoveries'][node['id']]['unknowns'][0]['blocking'])
        self.assertIn('b-result',(self.output/'functions'/node['id']/'candidate.md').read_text())
