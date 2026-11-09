"""Offline orchestration tests for function extraction and isolated spec workers."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from stage1.task import Budgets
from stage2.bundled import run_combined_pipeline as run_pipeline, export_examples
from stage2.inventory import expand_selection
from stage2.contracts import SECTIONS, CHECKS
from tests.test_stage2_inventory import selected


def decode_after(text, marker):
    return json.JSONDecoder().raw_decode(text.split(marker,1)[1])[0]

class BundleModel:
    def __init__(self, role, tid, harness):
        self.role=role;self.tid=tid;self.h=harness;self.steps=None;self.index=0
    def __call__(self, messages, timeout):
        system=messages[0]['content']
        if self.steps is None:
            if self.role=='extract_source':
                a=decode_after(system,'补充任务：');node=a['function']
            else:
                a=decode_after(system,'任务：\n');node=a['function']
            self.a=a;self.node=node
            if self.h.fail(self.role,node['symbol'],self.tid):raise RuntimeError('fixture worker interrupted')
            ids=decode_after(system,'Derived artifact IDs: ')
            self.steps=[{'tool':'artifact','id':i} for i in ids]
            if self.role=='extract_source':
                self.steps.append({'tool':'read','path':'lib/code.c','start':1,'count':4})
                if a.get('material_requests'):
                    self.steps.append({'tool':'read','path':'lib/config.h','start':1,'count':1})
            elif self.role=='write' and self.h.probe:
                self.steps.append({'tool':'read','path':'lib/secret.txt','start':1,'count':1})
        if self.index<len(self.steps):
            action=self.steps[self.index];self.index+=1;return json.dumps({**action,'draft':'fixture findings: inspect bounded source and preserve missing material'})
        artifacts={};reads=[];errors=[]
        for m in messages[1:]:
            if m['role']!='user':continue
            try:value=json.loads(m['content'])
            except ValueError:continue
            if value.get('kind')=='derived_interpretation_not_original_evidence':artifacts[value['id']]=value['content']
            if value.get('lines'):reads.append(value)
            if value.get('error'):errors.append(value['error'])
        node=self.node;ident=node['id'];symbol=node['symbol']
        if self.role=='write' and 'writer-schema' in artifacts:
            from stage2.context_cards import decode_writer_edges
            self.a['edges']=list(decode_writer_edges(artifacts).values())
        if self.role!='extract_source':
            for pack in artifacts['source-index']:
                for s in pack['ranges']:
                    if not any(v['path']==s['path'] and v['start']<=s['start']<=s['end']<=v['end'] for v in reads):
                        return json.dumps({'tool':'read','path':s['path'],'start':s['start'],'count':s['end']-s['start']+1,'draft':'fixture source inspection: own package and supplied adjacent ranges only'})
        if self.role=='extract_source':
            snippets=[];calls=[]
            if symbol=='a':
                snippets=[{'kind':'declaration','source':{'path':'lib/code.c','start':1,'end':1},'symbol':'b','reason':'direct call interface','condition':'always'}]
                calls=[{'symbol':'b','target_id':self.h.by_symbol['b']['id'],'declaration_index':0,'callsite':node['source'],'condition':'always','unresolved':''}]
            if self.a.get('material_requests'):
                snippets.append({'kind':'macro','source':{'path':'lib/config.h','start':1,'end':1},'symbol':'LIMIT','reason':'requested configuration','condition':'always'})
            report={'function_id':ident,'snippets':snippets,'calls':calls,'coverage':{k:'checked' for k in ('types','macros','declarations')},'unknowns':[]}
        elif self.role=='write':
            needs=self.h.request and symbol=='unrelated' and not any(s['path']=='lib/config.h' for p in artifacts['source-index'] for s in p['ranges'])
            report={'function_id':ident,'proof_status':'not_proved','sections':{k:'fixture explicit '+k for k in SECTIONS},
                    'claims':[{'id':'meaning','kind':'interpretation','text':'integer identity or increment','evidence':[node['source']]}],
                    'call_requirements':[{'edge_id':e['id'],'precondition':'integer x','postcondition':'returns x','status':'required_not_guaranteed','evidence':[e['callsite']]} for e in self.a['edges'] if e['caller']==ident],
                    'caller_scenarios':[],'reference_uses':[],'common_needs':[],'unknowns':[{'description':'need configuration','blocking':True}] if needs else [],
                    'material_requests':[{'symbol':'LIMIT','question':'what is LIMIT','reason':'configuration required'}] if needs else []}
        else:
            needs=artifacts['candidate'].get('material_requests',[])
            report={'function_id':ident,'verdict':'needs_revision' if needs else 'pass',
                    'checks':{k:'independent fixture check' for k in (*CHECKS,'bundle_completeness')},
                    'findings':[{'description':'need configuration','blocking':True}] if needs else [],
                    'evidence':[node['source']],'tool_evidence':[],'material_requests':needs}
        self.h.events.append({'role':self.role,'symbol':symbol,'tid':self.tid,'assignment':self.a,'artifacts':artifacts,'reads':reads,'errors':errors,'report':report})
        return json.dumps({'tool':'finish','report':report})

class Harness:
    def __init__(self, manifest, fail=None, probe=False, request=False):
        self.by_symbol={n['symbol']:n for n in manifest['functions']};self.events=[]
        self.fail=fail or (lambda role,symbol,tid:False);self.probe=probe;self.request=request
    def factory(self,role,tid):return BundleModel(role,tid,self)

class BundledPipelineTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.base=Path(self.tmp.name)
        self.root=self.base/'input';(self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text('int b(int x);\nint a(int x) { return b(x); }\nint b(int x) { return x; }\nint unrelated(int x) { return x+1; }\n')
        (self.root/'lib/config.h').write_text('#define LIMIT 100\n');(self.root/'lib/secret.txt').write_text('unextracted secret\n')
        self.manifest=expand_selection(self.root,selected());self.output=self.base/'run'
    def run_fixture(self,h=None,**kwargs):
        h=h or Harness(self.manifest)
        status=run_pipeline(self.root,self.output,self.manifest,{'module':'fixture module'},h.factory,
            budgets=Budgets(calls=24,seconds=30,context_chars=60000,reserve_seconds=0),batch_size=1,**kwargs)
        graph=json.loads((self.output/'graph.json').read_text())
        return status,graph,h
    def test_whole_group_finishes_and_group_review_reads_incoming_bundle(self):
        status,graph,h=self.run_fixture()
        self.assertEqual(status['status'],'candidates_reviewed',status)
        self.assertEqual(status['selection_progress']['reviewed_count'],3)
        group_b=next(e for e in h.events if e['symbol']=='b' and '-group-review-calls-' in e['tid'])
        a_source=h.by_symbol['a']['source']
        self.assertTrue(any(v['path']==a_source['path'] and v['start']<=a_source['start']<=v['end'] for v in group_b['reads']))
        self.assertIn('neighbor:'+h.by_symbol['a']['id'],group_b['artifacts'])
    def test_other_extraction_failure_does_not_block_valid_drafts(self):
        h=Harness(self.manifest,fail=lambda r,s,t:r=='extract_source' and s=='unrelated')
        status,graph,_=self.run_fixture(h)
        self.assertEqual(status['status'],'incomplete')
        for symbol in ('a','b'):
            ident=h.by_symbol[symbol]['id'];self.assertIsNotNone(graph['nodes'][ident]['spec'])
            self.assertTrue((self.output/'functions'/ident/'candidate.json').exists())
        self.assertIsNone(graph['nodes'][h.by_symbol['unrelated']['id']]['spec'])
    def test_writers_cannot_read_unextracted_original(self):
        status,graph,h=self.run_fixture(Harness(self.manifest,probe=True))
        self.assertEqual(status['status'],'candidates_reviewed',status)
        writes=[e for e in h.events if e['role']=='write'];self.assertEqual(len(writes),3)
        for e in writes:
            self.assertTrue(any('not_extracted' in error for error in e['errors']))
            self.assertFalse(any(v['path']=='lib/secret.txt' for v in e['reads']))
    def test_resume_reuses_successful_bundles_and_drafts(self):
        h=Harness(self.manifest,fail=lambda r,s,t:r=='extract_source' and s=='unrelated')
        _,graph,_=self.run_fixture(h)
        old={s:copy.deepcopy(graph['nodes'][h.by_symbol[s]['id']]) for s in ('a','b')}
        status,graph,resumed=self.run_fixture(resume=True)
        self.assertEqual(status['status'],'candidates_reviewed',status)
        self.assertFalse(any(e['symbol'] in ('a','b') and e['role'] in ('extract_source','write') for e in resumed.events))
        for s in ('a','b'):
            node=graph['nodes'][h.by_symbol[s]['id']]
            self.assertEqual(node['source_bundle'],old[s]['source_bundle']);self.assertEqual(node['spec'],old[s]['spec'])
    def test_review_failure_preserves_draft_and_bundle_for_resume(self):
        h=Harness(self.manifest,fail=lambda r,s,t:r=='review' and s=='unrelated')
        status,graph,_=self.run_fixture(h)
        ident=h.by_symbol['unrelated']['id'];node=graph['nodes'][ident]
        self.assertEqual(status['status'],'incomplete');self.assertIsNotNone(node['spec'])
        self.assertTrue((self.output/'functions'/ident/'candidate.json').exists())
        original_bundle=copy.deepcopy(node['source_bundle'])
        status,graph,resumed=self.run_fixture(resume=True)
        self.assertEqual(status['status'],'candidates_reviewed',status)
        self.assertEqual(graph['nodes'][ident]['source_bundle'],original_bundle)
        self.assertFalse(any(e['role']=='extract_source' and e['symbol']=='unrelated' for e in resumed.events))
        write=next(e for e in resumed.events if e['role']=='write' and e['symbol']=='unrelated')
        self.assertIn('previous_candidate',write['artifacts'])
    def test_material_request_routes_to_bounded_reextraction(self):
        status,graph,h=self.run_fixture(Harness(self.manifest,request=True),max_revisions=1)
        self.assertEqual(status['status'],'candidates_reviewed',status)
        extractions=[e for e in h.events if e['role']=='extract_source' and e['symbol']=='unrelated']
        self.assertEqual(len(extractions),2)
        self.assertEqual(extractions[1]['assignment']['material_requests'][0]['symbol'],'LIMIT')
        self.assertEqual(graph['nodes'][h.by_symbol['unrelated']['id']]['spec']['material_requests'],[])
    def test_zero_repair_budget_keeps_requested_material_gap(self):
        status,graph,h=self.run_fixture(Harness(self.manifest,request=True),max_revisions=0)
        self.assertEqual(status['status'],'incomplete')
        self.assertEqual(sum(e['role']=='extract_source' and e['symbol']=='unrelated' for e in h.events),1)
        self.assertEqual(graph['nodes'][h.by_symbol['unrelated']['id']]['status'],'needs_revision')
    def test_resume_refuses_modified_bundle(self):
        _,graph,h=self.run_fixture();node=graph['nodes'][h.by_symbol['a']['id']]
        (self.output/node['source_bundle']['path']/'implementation.c').write_text('modified\n')
        with self.assertRaisesRegex(ValueError,'bundle changed'):self.run_fixture(resume=True)
    def test_resume_refuses_modified_manifest(self):
        _,graph,h=self.run_fixture();node=graph['nodes'][h.by_symbol['a']['id']]
        path=self.output/node['source_bundle']['path']/'manifest.json';m=json.loads(path.read_text());m['configuration']='modified';path.write_text(json.dumps(m))
        with self.assertRaisesRegex(ValueError,'manifest changed'):self.run_fixture(resume=True)
    def test_export_new_directory_and_refuse_existing(self):
        self.run_fixture();destination=self.base/'qcp-examples'
        self.assertEqual(export_examples(self.output,destination),3)
        before=sorted(str(p.relative_to(destination)) for p in destination.rglob('*'))
        with self.assertRaisesRegex(ValueError,'new directory'):export_examples(self.output,destination)
        self.assertEqual(before,sorted(str(p.relative_to(destination)) for p in destination.rglob('*')))

if __name__=='__main__':unittest.main()
