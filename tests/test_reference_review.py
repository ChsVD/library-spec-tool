from tests.scenario_fixture import scenario
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from stage1.task import write_json
from stage2.inventory import expand_selection
from stage3.reference import run as run_reference, main
from functools import partial
run = partial(run_reference, graph_backend="lexical")
from stage3.reference_review import CHECKS, approved, validate_review, REVIEW_PROMPT
from stage4.pipeline import load_upstream
from stage2.graph import digest
from tests.test_stage2_inventory import selected


def review_row(ident, verdict='pass'):
    checks={key:{'decision':'pass','explanation':'Checked against fixture source and entry inputs.'}
            for key in CHECKS}
    findings=[]
    if verdict!='pass':
        checks['precise_output']['decision']='issue' if verdict=='needs_revision' else 'unknown'
        findings=[{'category':'precise_output','description':'Result needs clarification.',
                   'suggested_fix':'Bind the result to entry x, or identify missing evidence.','blocking':True}]
    return {'function_id':ident,'verdict':verdict,'checks':checks,'findings':findings}


class ReferenceReviewTests(unittest.TestCase):
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup)
        self.base=Path(tmp.name);self.root=self.base/'input'
        (self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text('int a(int x) { return b(x); }\nint b(int x) { return x; }\n')
        self.manifest=expand_selection(self.root,selected())
        self.output=self.base/'out';self.calls=[];self.sessions=[]
        self.mode='pass'

    def factory(self,ident):
        self.sessions.append(ident)
        def model(messages,timeout):
            a=json.loads(messages[1]['content'])
            role='review' if messages[0]['content']==REVIEW_PROMPT else ('revision' if 'review_feedback' in a else 'write')
            self.calls.append((role,a,copy.deepcopy(messages)))
            if role=='review':
                if self.mode=='error':raise RuntimeError('review backend unavailable')
                if self.mode=='interrupt':raise KeyboardInterrupt()
                if self.mode=='malformed':return '{bad'
                verdict=self.mode if self.mode in ('needs_revision','insufficient') else 'pass'
                if self.mode=='revise_once' and not any(x[0]=='revision' for x in self.calls):
                    verdict='needs_revision'
                rows=[review_row(n['id'],verdict) for n in a['assigned']]
            else:
                rows=[{'function_id':n['id'],'scenario_analysis':scenario(a),'observations':'Returns callee value or x.',
                       'suggested_spec':'Ensure ret=x'+(' (revised)' if role=='revision' else ''),
                       'assumptions':'No additional assumptions; call graph may be incomplete.',
                       'callee_requirements':[{'callee':'b','requirement':'Return entry x'+(' revised' if role=='revision' else '')}]}
                      for n in a['assigned']]
            return json.dumps({'tool':'finish','report':{'functions':rows}})
        return model

    def execute(self,**kwargs):
        return run(self.root,self.output,self.manifest,{},self.factory,**kwargs)

    def test_independent_review_and_downstream_handoff(self):
        graph=self.execute()
        self.assertTrue(all(approved(n) for n in graph['nodes'].values()))
        self.assertEqual([x[0] for x in self.calls],['write','review','write','review'])
        for role,a,messages in self.calls:
            if role=='review':
                self.assertEqual(len(messages),2)
                self.assertTrue(a['assigned'][0]['code'])
                self.assertTrue(a['candidate_specs'])
        loaded,_,_=load_upstream(self.root,self.output)
        self.assertTrue(loaded['upstream_context']['semantic_review'])
        self.assertFalse(loaded['upstream_context']['proved'])
        before=len(self.calls);self.execute(resume=True);self.assertEqual(len(self.calls),before)

    def test_revision_then_new_independent_review(self):
        self.mode='revise_once';graph=self.execute()
        self.assertEqual([x[0] for x in self.calls],['write','review','revision','review','write','review'])
        child=next(a for role,a,_ in self.calls if role=='write' and a['assigned'][0]['symbol']=='b')
        self.assertIn('revised',child['incoming'][0]['requirements'][0]['requirement'])
        self.assertEqual(len(self.sessions),len(set(self.sessions)))
        self.assertTrue(all(approved(n) for n in graph['nodes'].values()))

    def test_revision_exhaustion_blocks_callee_and_stage3(self):
        self.mode='needs_revision';graph=self.execute(max_revisions=1)
        by_name={n['symbol']:n for n in graph['nodes'].values()}
        self.assertEqual(by_name['a']['status'],'review_needs_revision')
        self.assertEqual(by_name['b']['status'],'upstream_incomplete')
        self.assertEqual([x[0] for x in self.calls],['write','review','revision','review'])
        self.assertTrue(by_name['a']['spec'])
        self.assertFalse(next(iter(graph['edges'].values()))['requirements'])
        with self.assertRaises(ValueError):load_upstream(self.root,self.output)
        self.assertEqual(len(list((self.output/'tasks').rglob('accepted.json'))),3)

    def test_insufficient_does_not_spend_revision(self):
        self.mode='insufficient';graph=self.execute()
        self.assertEqual([x[0] for x in self.calls],['write','review'])
        self.assertIn('review_insufficient',[n['status'] for n in graph['nodes'].values()])

    def test_backend_failure_resume_keeps_draft_and_history(self):
        self.mode='error';graph=self.execute()
        self.assertEqual([x[0] for x in self.calls],['write','review'])
        self.assertIn('review_failed',[n['status'] for n in graph['nodes'].values()])
        old={str(p):p.read_bytes() for p in (self.output/'tasks').rglob('*') if p.is_file()}
        self.calls=[];self.mode='pass';self.execute(resume=True)
        self.assertEqual([x[0] for x in self.calls],['review','write','review'])
        for path,content in old.items():self.assertEqual(Path(path).read_bytes(),content)

    def test_interrupt_saves_pending_draft_for_review(self):
        self.mode='interrupt'
        with self.assertRaises(KeyboardInterrupt):self.execute()
        graph=json.loads((self.output/'graph.json').read_text())
        self.assertIn('pending_review',[n['status'] for n in graph['nodes'].values()])
        self.calls=[];self.mode='pass';self.execute(resume=True)
        self.assertEqual(self.calls[0][0],'review')

    def test_format_repair_is_bounded_and_never_passes_invalid_review(self):
        self.mode='malformed';graph=self.execute()
        self.assertEqual([x[0] for x in self.calls],['write','review','review'])
        self.assertFalse(any(approved(n) for n in graph['nodes'].values()))

    def test_review_validation_rejects_false_pass_and_missing_coverage(self):
        row=review_row('a');row['findings']=[{'category':'precise_output','description':'wrong',
            'suggested_fix':'fix','blocking':True}]
        with self.assertRaises(ValueError):validate_review({'functions':[row]},['a'])
        with self.assertRaises(ValueError):validate_review({'functions':[review_row('a')]},['a','b'])
        row=review_row('a');del row['checks']['memory_resources']
        with self.assertRaises(ValueError):validate_review({'functions':[row]},['a'])
        row=review_row('a');row['checks']['precise_output']['decision']='unknown'
        with self.assertRaises(ValueError):validate_review({'functions':[row]},['a'])

    def test_changed_spec_cannot_reuse_pass(self):
        self.execute()
        path=self.output/'graph.json';g=json.loads(path.read_text())
        next(iter(g['nodes'].values()))['spec']['suggested_spec']='arbitrary result'
        write_json(path,g)
        status=json.loads((self.output/'status.json').read_text())
        status['graph_digest']=digest(g);write_json(self.output/'status.json',status)
        with self.assertRaisesRegex(ValueError,'stale'):load_upstream(self.root,self.output)

    def test_plan_does_not_call_models(self):
        self.execute(prepare_only=True)
        self.assertFalse(self.calls)
        self.assertFalse(json.loads((self.output/'status.json').read_text())['semantic_review'])

    def test_explicit_skip_review_retains_unreviewed_status(self):
        self.execute(review=False)
        self.assertTrue(all(role=='write' for role,_,_ in self.calls))
        graph,_,_=load_upstream(self.root,self.output)
        self.assertFalse(graph['upstream_context']['semantic_review'])

    def test_cli_does_not_handoff_review_failure(self):
        argv=['stage2','--manifest','fixture','--output',str(self.output),'--with-common']
        with patch('sys.argv',argv),patch('stage3.reference.load_manifest',return_value=(self.manifest,{})), \
             patch('stage1.codex_backend.CodexModel'), \
             patch('stage3.reference.run',return_value={'nodes':{'a':{'status':'review_failed'}},'components':[]}), \
             patch('stage4.pipeline.run_pipeline') as downstream,patch('builtins.print'):
            self.assertEqual(main(),1);downstream.assert_not_called()


    def test_changed_caller_invalidates_downstream_review(self):
        self.execute()
        path=self.output/'graph.json';g=json.loads(path.read_text())
        parent=next(n for n in g['nodes'].values() if n['symbol']=='a')
        parent['spec']['suggested_spec']='Ensure ret=x with clarified input'
        write_json(path,g)
        status=json.loads((self.output/'status.json').read_text())
        status['graph_digest']=digest(g);write_json(self.output/'status.json',status)
        self.calls=[];self.execute(resume=True)
        self.assertEqual([role for role,_,_ in self.calls],['review','review'])
        self.assertEqual([a['assigned'][0]['symbol'] for _,a,_ in self.calls],['a','b'])

    def test_review_context_overflow_is_saved_without_review_call(self):
        from stage3.reference_review import review_cycle
        records=[{'function_id':'a'}]
        assignment={'assigned':[{'id':'a','code':'x'*12000}]}
        rows,reviews,status=review_cycle(self.factory,'fixture',assignment,records,
            self.base/'budget','writer',lambda r,ids:r,10000,1,1)
        self.assertEqual(status,'review_failed')
        self.assertEqual(rows,records)
        self.assertFalse(self.calls)
        self.assertTrue((self.base/'budget/review-0/input.json').exists())


    def test_reviewed_drafts_complete_stage3_with_proof_status_unchanged(self):
        from stage1.task import Budgets
        from stage4.pipeline import run_pipeline
        from tests.test_reference_stage3 import ReferenceCommonModel
        path=self.root/'lib/code.c';path.write_text(path.read_text()+'// fixture evidence boundary\n')
        self.manifest=expand_selection(self.root,selected())
        self.execute()
        result=run_pipeline(self.root,self.base/'common',self.output,
            lambda role,ident:ReferenceCommonModel(role),
            protocol_version=2,budgets=Budgets(calls=24,seconds=30,context_chars=60000,reserve_seconds=0))
        self.assertEqual(result['status'],'common_candidates_reviewed')
        self.assertTrue(result['upstream_context']['semantic_review'])
        self.assertEqual(result['proof_status'],'not_proved')
