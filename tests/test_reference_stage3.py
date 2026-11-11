import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from stage1.task import Budgets, write_json
from stage2.inventory import expand_selection
from stage3.reference import run as run_reference, main
from functools import partial
# Compatibility tests for older/unreviewed reference input.
run=partial(run_reference,review=False,graph_backend="lexical")
from stage4.pipeline import load_upstream, run_pipeline
from stage4 import contracts
from tests.test_stage2_inventory import selected
from tests import test_reference_specs as reference_fixtures
from tests.test_stage3 import Model


class ReferenceCommonModel(Model):
    def __call__(self, messages, timeout):
        action=json.loads(super().__call__(messages, timeout))
        context=None
        for message in messages[1:]:
            if message['role']!='user': continue
            try: value=json.loads(message['content'])
            except ValueError: continue
            if value.get('id')=='upstream-context':
                context=value['content']
        if action.get('tool')=='finish':
            assert isinstance(context['semantic_review'],bool)
            assert context['proved'] is False
            conditions=context['conditions']
            if self.role=='common':
                action['report']['upstream_conditions']=conditions
            elif self.role=='review':
                action['report']['upstream_condition_checks']=[
                    {'function_id':f,'assumption_id':a['id'],'decision':'preserved',
                     'explanation':'Retained as an unverified assumption.'}
                    for f,rows in conditions.items() for a in rows]
        return json.dumps(action)


class ReferenceStage3Tests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name); self.root=self.base/'input'
        (self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text(
            'int a(int x) { return b(x); }\nint b(int x) { return x; }\n'
            'int unrelated(int x) { return x+1; }\n')
        self.manifest=expand_selection(self.root,selected())
        self.source=self.base/'reference'
        self.output=self.base/'common'
        self.factory=reference_fixtures.ReferenceTests().factory([])
        self.budgets=Budgets(calls=24,seconds=30,context_chars=60000,reserve_seconds=0)

    def generate(self, **kwargs):
        return run(self.root,self.source,self.manifest,{},self.factory,**kwargs)

    def common(self, **kwargs):
        return run_pipeline(self.root,self.output,self.source,
            kwargs.pop('factory',lambda role,ident:ReferenceCommonModel(role)),
            budgets=self.budgets,protocol_version=2,**kwargs)

    def test_complete_chain_preserves_unreviewed_inputs_and_resumes(self):
        self.generate()
        before={p.name:p.read_bytes() for p in self.source.glob('*.json')}
        result=self.common()
        self.assertEqual(result['status'],'common_candidates_reviewed')
        self.assertFalse(result['upstream_context']['semantic_review'])
        candidate=json.loads((self.output/'candidate.json').read_text())
        self.assertEqual(candidate['proof_status'],'not_proved')
        _,nodes,_=load_upstream(self.root,self.source)
        self.assertEqual(candidate['upstream_conditions'],contracts.upstream_conditions(nodes))
        self.assertEqual(before,{p.name:p.read_bytes() for p in self.source.glob('*.json')})
        def fail(*args): raise AssertionError('completed resume called model')
        self.assertEqual(self.common(resume=True,factory=fail)['status'],'common_candidates_reviewed')

    def test_partial_and_planned_runs_rejected(self):
        self.generate(max_components=1)
        with self.assertRaisesRegex(ValueError,'complete all'):
            load_upstream(self.root,self.source)
        self.generate(resume=True,prepare_only=True)
        with self.assertRaisesRegex(ValueError,'complete all'):
            load_upstream(self.root,self.source)

    def test_changed_snapshot_and_stale_marker_rejected(self):
        self.generate()
        write_json(self.source/'input_changed.json',{'results_stale':True})
        with self.assertRaisesRegex(ValueError,'stale'): load_upstream(self.root,self.source)
        (self.source/'input_changed.json').unlink()
        (self.root/'lib/code.c').write_text('changed')
        with self.assertRaisesRegex(ValueError,'input differs'): load_upstream(self.root,self.source)

    def test_tampered_graph_rejected(self):
        self.generate()
        path=self.source/'graph.json'; graph=json.loads(path.read_text())
        graph['nodes'].pop(next(iter(graph['nodes'])))
        write_json(path,graph)
        with self.assertRaisesRegex(ValueError,'mismatch'): load_upstream(self.root,self.source)

    def test_old_reference_output_and_missing_member(self):
        self.generate()
        path=self.source/'status.json'; status=json.loads(path.read_text())
        for k in ('workflow','graph_digest','expected_function_ids'): status.pop(k)
        write_json(path,status)
        self.assertEqual(len(load_upstream(self.root,self.source)[1]),3)
        path=self.source/'graph.json'; graph=json.loads(path.read_text())
        graph['nodes'].pop(next(iter(graph['nodes']))); write_json(path,graph)
        with self.assertRaisesRegex(ValueError,'scope'): load_upstream(self.root,self.source)

    def test_dropped_assumptions_cannot_pass_candidate(self):
        self.generate()
        class Dropping(ReferenceCommonModel):
            def __call__(self,messages,timeout):
                action=json.loads(super().__call__(messages,timeout))
                if self.role=='common' and action.get('tool')=='finish':
                    action['report'].pop('upstream_conditions',None)
                return json.dumps(action)
        result=self.common(factory=lambda role,ident:Dropping(role))
        self.assertEqual(result['status'],'incomplete')
        self.assertFalse((self.output/'candidate.json').exists())

    def test_changed_upstream_refuses_completed_resume(self):
        self.generate(); self.assertEqual(self.common()['status'],'common_candidates_reviewed')
        path=self.source/'status.json'; status=json.loads(path.read_text())
        status['status']='partial'; write_json(path,status)
        with self.assertRaises(ValueError): self.common(resume=True)

    def test_default_cli_handoff_only_for_complete_nonplanning_run(self):
        for states,prepare,expected in [
            (['reference_draft'],False,True),
            (['reference_draft','pending'],False,False),
            (['reference_draft'],True,False)]:
            with self.subTest(states=states,prepare=prepare):
                graph={'nodes':{str(i):{'status':s} for i,s in enumerate(states)},'components':[]}
                argv=['stage2','--manifest','fixture','--output',str(self.source),'--with-common','--skip-review']
                if prepare: argv.append('--prepare-only')
                with patch('sys.argv',argv), patch('stage3.reference.load_manifest',return_value=({},{})), \
                     patch('stage3.reference.run',return_value=graph), patch('stage1.codex_backend.CodexModel'), \
                     patch('stage4.pipeline.run_pipeline',return_value={'status':'common_candidates_reviewed'}) as downstream, \
                     patch('builtins.print'):
                    result=main()
                    self.assertEqual(downstream.called,expected)
                    if 'pending' in states: self.assertEqual(result,1)


    def test_unknown_calls_and_scope_gaps_are_preserved(self):
        (self.root/'lib/code.c').write_text(
            'int a(int x) { return MISSING(x); }\nint b(int x) { return x; }\n'
            'int unrelated(int x) { return x+1; }\n')
        self.manifest=expand_selection(self.root,selected())
        self.manifest['selection_inventory']['gaps']=['unresolved configuration']
        original=self.generate()
        graph,nodes,_=load_upstream(self.root,self.source)
        self.assertEqual(graph['upstream_context']['unknown_calls'],original['unknown_calls'])
        self.assertEqual(graph['upstream_context']['inventory_gaps'],['unresolved configuration'])
        self.assertFalse(graph['upstream_context']['proved'])
        self.assertEqual(len(nodes),3)
