import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from stage2.conditional import inspect, review_checks
from stage2.review_flow import run_review, jobs
from stage2.pipeline import render
from stage1.task import Budgets


class ConditionalTests(unittest.TestCase):
    def setUp(self):
        self.missing_source=False
        self.node={'id':'f','symbol':'f','source':{'path':'f.c','start':1,'end':1},'configuration':'all','materials':[]}
        edge={'id':'e','caller':'f','callee':'d','certainty':'conditional','callsite':self.node['source'],'condition':'always'}
        self.graph={'nodes':{'f':{**self.node,'spec':None},'d':{'id':'d','symbol':'dep','spec':None}},'edges':{'e':edge},'discoveries':{}}
        gap={'description':'dep result contract missing','blocking':True,'category':'dependency_contract','symbol':'dep'}
        self.extract={'unknowns':[gap],'coverage':{'calls':'checked'},'snippets':[]}
        self.assumption={'id':'dep-result','symbol':'dep','condition':'Assume dep returns the sum.',
                         'affected_claim_ids':['result'],'explanation':'Required to infer this wrapper result.',
                         'gaps':[{'source':'extraction_unknowns','index':0},{'source':'material_requests','index':0}]}
        self.spec={'function_id':'f','proof_status':'not_proved',
                   'sections':{k:'Assume dep returns the sum.' for k in ('meaning','environment','preconditions','postconditions','effects','boundaries')},
                   'claims':[{'id':'result','kind':'candidate','text':'Returns sum under assumption.','evidence':[]}],
                   'reference_uses':[],'call_requirements':[],'caller_scenarios':[],'unknowns':[],
                   'material_requests':[{'symbol':'dep','category':'dependency_contract','question':'return guarantee?','reason':'wrapper result'}],
                   'conditional_assumptions':[self.assumption]}

    def test_precise_conditions_only(self):
        errors,covered=inspect(self.spec,self.extract,self.graph,'f')
        self.assertEqual(errors,[])
        self.assertEqual(covered,{('extraction_unknowns',0),('material_requests',0)})
        for mutation in ('category','quote','claim','index','callee'):
            spec,extract,graph=copy.deepcopy((self.spec,self.extract,self.graph))
            if mutation=='category':extract['unknowns'][0].pop('category')
            if mutation=='quote':spec['conditional_assumptions'][0]['condition']='unquoted'
            if mutation=='claim':spec['claims'][0]['kind']='source_fact'
            if mutation=='index':spec['conditional_assumptions'][0]['gaps'][0]['index']=10
            if mutation=='callee':graph['edges']['e']['callee']=None
            errors,covered=inspect(spec,extract,graph,'f')
            self.assertTrue(errors,mutation)
            self.assertFalse(covered,mutation)

    def run_review(self,decision='acceptable_condition'):
        calls=[]
        def fake_task(root,folder,factory,prompt,validator,**kw):
            candidate=kw['artifacts']['candidate']; calls.append(kw)
            self.assertEqual(candidate['conditional_assumptions'],[self.assumption])
            self.assertTrue(candidate['claims'])
            self.assertIn('conditional-gaps',kw['artifacts'])
            report={'function_id':'f','verdict':'pass' if decision=='acceptable_condition' else 'needs_revision',
                    'checks':{k:'checked' for k in validator.keywords['keys']},'findings':[],
                    'material_requests':[],'evidence':[],
                    'assumption_checks':[{'id':'dep-result','decision':decision,'explanation':'Independently assessed.'}]}
            self.assertEqual(review_checks(report,[self.assumption]),[])
            return {'status':'task_completed','calls':1,'report':report}
        missing_source=self.missing_source
        class Reader:
            def __init__(self,*a,**k):pass
            def execute(self,a):return {'error':'not in bundle'} if missing_source else {'end':a['start']+a['count']-1}
        with tempfile.TemporaryDirectory() as tmp, patch('stage2.review_flow.BundleReader',Reader), patch('stage2.review_flow.run_task',fake_task), patch('stage2.review_flow.source_index',return_value={}):
            result=run_review(Path(tmp),Path(tmp)/'review',lambda *a:None,node=self.node,spec=self.spec,graph=self.graph,artifacts={},bundles=[(None,{'report':self.extract})],budgets=Budgets(),label='test')
        return result,calls

    def test_review_reached_and_assumptions_preserved(self):
        result,calls=self.run_review()
        self.assertEqual(len(calls),3)
        self.assertEqual(result['report']['verdict'],'pass')
        self.assertEqual(result['report']['conditional_assumptions'],[self.assumption])
        self.assertEqual(result['report']['acceptance_scope'],'conditional_candidate_not_proved')
        self.assertIn('dep-result',render(self.spec))

    def test_independent_rejection_prevents_acceptance(self):
        result,_=self.run_review('reject')
        self.assertEqual(result['report']['verdict'],'needs_revision')
        self.assertTrue(review_checks({'verdict':'pass','assumption_checks':[{'id':'dep-result','decision':'reject','explanation':'circular'}]},[self.assumption]))
        self.assertTrue(review_checks({'verdict':'pass'},[self.assumption]))

    def test_missing_conditions_and_hard_gaps_still_block(self):
        for cause in ('unclassified','no_assumptions','coverage','unresolved','missing_source'):
            self.setUp()
            if cause=='missing_source':self.missing_source=True
            if cause=='unclassified':self.extract['unknowns'][0].pop('category')
            if cause=='no_assumptions':self.spec.pop('conditional_assumptions')
            if cause=='coverage':self.extract['coverage']['macros']='unknown'
            if cause=='unresolved':self.graph['discoveries']['f']={'coverage':{'outgoing':'unknown'}}
            result,calls=self.run_review()
            self.assertFalse(calls,cause)
            self.assertEqual(result['reason'],'preflight_requires_material')
