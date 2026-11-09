import copy
import json
from pathlib import Path
import tempfile
import unittest

from stage1.reader import Reader
from stage1.task import Budgets
from stage2.graph import new_graph, layers, context, merge_discovery, install_spec, validate_manifest
from stage2.contracts import discovery, specification, review, SECTIONS, CHECKS
from stage2.pipeline import run_pipeline, load_manifest, material_pages


def source(line=1): return {'path':'lib/code.c','start':line,'end':line}
def node(ident,line): return {'id':ident,'symbol':ident,'configuration':'generic','source':source(line),'materials':['module']}
def manifest(): return {'version':1,'scope_decision':'test selected a and b','materials':{'module':{}},'functions':[node('a',1),node('b',2)]}
def edge(): return {'id':'a-b-line1','caller':'a','callee':'b','certainty':'direct','condition':'always','callsite':source()}
def spec(ident='a'):
    return {'function_id':ident,'proof_status':'not_proved','sections':{k:'明确条件和功能'+k for k in SECTIONS},
      'claims':[{'id':'meaning','kind':'interpretation','text':'returns argument','evidence':[source(1 if ident=='a' else 2)]}],
      'call_requirements':([{'edge_id':'a-b-line1','precondition':'任意整数x','postcondition':'返回x','status':'required_not_guaranteed','evidence':[source()]}] if ident=='a' else []),
      'reference_uses':[],'common_needs':[],'unknowns':[]}
def reviewed(ident='a',verdict='pass'):
    return {'function_id':ident,'verdict':verdict,'checks':{k:'检查依据及限制' for k in CHECKS},
            'findings':[] if verdict=='pass' else [{'description':'应写清返回值与输入的关系','blocking':True}],
            'evidence':[source(1 if ident=='a' else 2)],'tool_evidence':[]}
def discovered(ident):
    return {'function_id':ident,'neighbors':[], 'edges':[edge()],
            'coverage':{'outgoing':'checked_scope','incoming':'只查本夹具文件'},'unknowns':[]}


class Model:
    def __init__(self,role,tid,fail=False,revise=False,seen=None):
        self.role=role;self.tid=tid;self.fail=fail;self.revise=revise;self.seen=seen
    def __call__(self,messages,timeout):
        if self.fail: raise RuntimeError('simulated interruption')
        system=messages[0]['content']
        assignment=json.loads(system.split('任务：\n',1)[1].split('\n\nTask budgets:')[0])
        ident=assignment['function']['id']
        delivered=[]; source_read=False; candidate=None
        for m in messages[1:]:
            if m['role']!='user':continue
            try:v=json.loads(m['content'])
            except ValueError:continue
            if v.get('kind')=='derived_interpretation_not_original_evidence':
                delivered.append(v['id'])
                if v['id']=='candidate':candidate=v['content']
            if v.get('path')=='lib/code.c' and v.get('lines'):source_read=True
        ids=json.loads(system.split('Derived artifact IDs: ')[1])
        for artifact in ids:
            if artifact not in delivered:
                return json.dumps({'tool':'artifact','id':artifact,'draft':'已读取局部材料，继续核对原文'})
        if not source_read:return json.dumps({'tool':'read','path':'lib/code.c','start':1,'count':3,'draft':'核对完整局部函数与调用点'})
        if self.role=='discover':report=discovered(ident)
        elif self.role=='write':
            report=spec(ident)
            if self.revise and ident=='a' and 'previous_candidate' not in ids:report['sections']['postconditions']='range-only'
        else:
            verdict='needs_revision' if candidate['sections']['postconditions']=='range-only' else 'pass'
            report=reviewed(ident,verdict)
        if self.seen is not None:self.seen.append((self.role,ident,assignment,ids))
        return json.dumps({'tool':'finish','report':report},ensure_ascii=False)


class Stage2Tests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.base=Path(self.tmp.name)
        self.root=self.base/'input';(self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text('int a(int x) { return b(x); }\nint b(int x) { return x; }\n// end\n')
        self.reader=Reader(self.root,self.base/'reads.jsonl')
        self.reader.execute({'tool':'read','path':'lib/code.c','start':1,'count':3})
        self.graph=new_graph(manifest());merge_discovery(self.graph,discovered('a'));merge_discovery(self.graph,discovered('b'))
    def tearDown(self):self.tmp.cleanup()
    def run_fixture(self,output='run',**kwargs):
        factory=kwargs.pop('factory',lambda role,tid:Model(role,tid))
        return run_pipeline(self.root,self.base/output,manifest(),{'module':'module explanation'},factory,
            budgets=Budgets(calls=16,seconds=30,context_chars=60000,reserve_seconds=0),**kwargs)
    def test_topdown_and_cycles(self):
        self.assertEqual(layers(self.graph),[[['a']],[['b']]])
        self.graph['edges']['back']={**edge(),'id':'back','caller':'b','callee':'a','callsite':source(2)}
        self.assertEqual(layers(self.graph),[[['a','b']]])
    def test_context_excludes_unrelated_and_transitive(self):
        self.graph['nodes']['c']={**node('c',3),'selected':True,'spec':None,'revision':0,'status':'pending'}
        self.graph['edges']['bc']={**edge(),'id':'bc','caller':'b','callee':'c','callsite':source(2)}
        value=context(self.graph,'a')
        self.assertEqual([x['id'] for x in value['neighbors']],['b'])
        with self.assertRaisesRegex(ValueError,'context_limit'):context(self.graph,'a',10)
    def test_discovery_needs_full_original_read(self):
        reader=Reader(self.root,self.base/'other.jsonl')
        self.assertTrue(discovery(discovered('a'),reader,set(),node=node('a',1),known=self.graph['nodes']))
    def test_discovery_bad_endpoint_and_callsite(self):
        r=discovered('a');r['edges'][0]['callee']='missing'
        self.assertTrue(discovery(r,self.reader,set(),node=node('a',1),known=self.graph['nodes']))
        r=discovered('a');r['edges'][0]['callsite']=source(2)
        self.assertTrue(discovery(r,self.reader,set(),node=node('a',1),known=self.graph['nodes']))
    def test_conflicting_merge_is_atomic(self):
        before=copy.deepcopy(self.graph);r=discovered('b');r['edges'][0]['condition']='different'
        with self.assertRaises(ValueError):merge_discovery(self.graph,r)
        self.assertEqual(before,self.graph)
    def test_unknown_call_is_retained(self):
        r=discovered('a');r['edges'][0].update(callee=None,certainty='unresolved',unresolved_target='callback')
        g=new_graph(manifest());merge_discovery(g,r)
        self.assertIsNone(g['edges']['a-b-line1']['callee'])
        self.assertIn('callback',json.dumps(context(g,'a')))
    def test_spec_requires_each_outgoing_scenario(self):
        s=spec();s['call_requirements']=[]
        self.assertTrue(specification(s,self.reader,{'material:module:1'},node=node('a',1),graph=self.graph))
        s=spec();s['call_requirements'][0]['status']='proved'
        self.assertTrue(specification(s,self.reader,{'material:module:1'},node=node('a',1),graph=self.graph))
    def test_forged_evidence_and_proof_rejected(self):
        s=spec();s['proof_status']='proved'
        self.assertTrue(specification(s,self.reader,{'material:module:1'},node=node('a',1),graph=self.graph))
        s=spec();s['claims'][0]['evidence']=[source(30)]
        self.assertTrue(specification(s,self.reader,{'material:module:1'},node=node('a',1),graph=self.graph))
    def test_review_unknown_and_tool_blocking(self):
        s=spec();s['unknowns']=[{'description':'core unknown','blocking':True}]
        self.assertTrue(review(reviewed(),self.reader,{'candidate'},node=node('a',1),spec=s,graph=self.graph))
        self.assertTrue(review(reviewed(verdict='tool_blocked'),self.reader,{'candidate'},node=node('a',1),spec=spec(),graph=self.graph))
    def test_reference_must_be_independently_read(self):
        s=spec();s['reference_uses']=[{'adaptation':'adapt','limitations':'unproved','evidence':[source(3)]}]
        reader=Reader(self.root,self.base/'review.jsonl');reader.execute({'tool':'read','path':'lib/code.c','start':1,'count':1})
        self.assertTrue(review(reviewed(),reader,{'candidate'},node=node('a',1),spec=s,graph=self.graph))
    def test_neighbor_update_invalidates_review(self):
        install_spec(self.graph,'a',spec(),reviewed())
        install_spec(self.graph,'b',spec('b'),reviewed('b'))
        self.assertEqual(self.graph['nodes']['a']['status'],'needs_recheck')
        self.assertEqual(self.graph['edges']['a-b-line1']['requirements'][0]['caller_revision'],1)
    def test_pipeline_rechecks_latest_neighbor_and_resume(self):
        seen=[]
        result=self.run_fixture(factory=lambda r,t:Model(r,t,seen=seen))
        self.assertEqual(result['status'],'candidates_reviewed',result)
        self.assertEqual(sum(r=='review' and i=='a' for r,i,_,_ in seen),2)
        b=next(a for r,i,a,_ in seen if r=='write' and i=='b')
        self.assertEqual(b['edges'][0]['requirements'][0]['status'],'required_not_guaranteed')
        result=self.run_fixture(resume=True,factory=lambda r,t: self.fail('completed task should be reused'))
        self.assertEqual(result['status'],'candidates_reviewed')
        self.assertTrue((self.base/'run/functions/a/candidate.md').exists())
    def test_finite_revision_uses_prior_review(self):
        result=self.run_fixture(factory=lambda r,t:Model(r,t,revise=True))
        self.assertEqual(result['status'],'candidates_reviewed',result)
        graph=json.loads((self.base/'run/graph.json').read_text())
        self.assertNotEqual(graph['nodes']['a']['spec']['sections']['postconditions'],'range-only')
    def test_no_revision_budget_preserves_rejection(self):
        result=self.run_fixture(max_revisions=0,factory=lambda r,t:Model(r,t,revise=True))
        self.assertEqual(result['status'],'incomplete')
        self.assertEqual(result['functions']['a'],'needs_revision')
    def test_failure_keeps_completed_work(self):
        result=self.run_fixture(factory=lambda r,t:Model(r,t,fail=r=='write' and '-b-' in t))
        self.assertEqual(result['status'],'incomplete')
        graph=json.loads((self.base/'run/graph.json').read_text())
        self.assertIsNotNone(graph['nodes']['a']['spec'])
        self.assertEqual(graph['nodes']['b']['status'],'incomplete')
        result=self.run_fixture(resume=True)
        self.assertEqual(result['status'],'candidates_reviewed',result)
    def test_resume_rejects_changed_input(self):
        self.run_fixture()
        (self.root/'lib/code.c').write_text('changed')
        with self.assertRaises(ValueError):self.run_fixture(resume=True)
    def test_material_paging_and_hash_check(self):
        pages=material_pages(node('a',1),{'module':'x'*13000})
        self.assertEqual(len(pages),3)
        self.assertTrue(all(len(p['text'])<=6000 for p in pages.values()))
        m=manifest();m['materials']={'module':{'path':'material.md','sha256':'wrong'}}
        (self.base/'material.md').write_text('module');(self.base/'manifest.json').write_text(json.dumps(m))
        with self.assertRaisesRegex(ValueError,'material changed'):load_manifest(self.base/'manifest.json')
    def test_cyclic_batch_rechecks_without_assuming_proofs(self):
        class CyclicModel(Model):
            def __call__(self,messages,timeout):
                result=json.loads(super().__call__(messages,timeout))
                if result.get('tool')=='finish':
                    r=result['report']
                    back={**edge(),'id':'back','caller':'b','callee':'a','callsite':source(2)}
                    if self.role=='discover':r['edges'].append(back)
                    elif self.role=='write' and r['function_id']=='b':
                        r['call_requirements']=[{'edge_id':'back','precondition':'x','postcondition':'x',
                                                'status':'required_not_guaranteed','evidence':[source(2)]}]
                return json.dumps(result)
        result=self.run_fixture(factory=lambda r,t:CyclicModel(r,t),batch_size=2,concurrency=2)
        self.assertEqual(result['status'],'candidates_reviewed',result)
        schedule=json.loads((self.base/'run/schedule.json').read_text())
        self.assertEqual(schedule,[[['a','b']]])
        graph=json.loads((self.base/'run/graph.json').read_text())
        self.assertTrue(all(n['spec']['proof_status']=='not_proved' for n in graph['nodes'].values()))
    def test_unknown_discovery_cannot_pass_review(self):
        self.graph['discoveries']['a']['coverage']['outgoing']='unknown'
        self.assertTrue(review(reviewed(),self.reader,{'candidate'},node=node('a',1),spec=spec(),graph=self.graph))
    def test_input_mutation_midrun_is_not_publishable(self):
        class Mutator(Model):
            def __call__(inner,messages,timeout):
                result=super().__call__(messages,timeout)
                if inner.role=='review' and json.loads(result).get('tool')=='finish':
                    (self.root/'new.txt').write_text('changed')
                return result
        result=self.run_fixture(factory=lambda r,t:Mutator(r,t))
        self.assertEqual(result['status'],'input_changed',result)
    def test_snapshot_context_does_not_grow_with_other_modules(self):
        before=context(self.graph,'a')
        for i in range(1000):
            self.graph['nodes']['other-'+str(i)]={**node('other-'+str(i),3),'selected':False,'spec':{'huge':'x'*1000},'revision':1,'status':'context_only'}
        self.assertEqual(before,context(self.graph,'a'))
    def test_resume_rejects_modified_graph_and_model(self):
        self.run_fixture()
        with self.assertRaisesRegex(ValueError,'model differs'):
            self.run_fixture(resume=True,model_identity={'model':'different'})
        p=self.base/'run/graph.json';g=json.loads(p.read_text());g['nodes']['a']['status']='proved';p.write_text(json.dumps(g))
        with self.assertRaisesRegex(ValueError,'checkpoint graph/status mismatch'):self.run_fixture(resume=True)
    def test_incoming_scenarios_cannot_be_outgoing_requirements(self):
        s=spec('b')
        s['caller_scenarios']=[{'edge_id':'a-b-line1','provided_conditions':'任意整数',
                              'needed_guarantees':'返回输入','status':'inferred_usage_not_guaranteed','evidence':[source()]}]
        self.assertEqual(specification(s,self.reader,{'material:module:1'},node=node('b',2),graph=self.graph),[])
        s['call_requirements']=[{'edge_id':'a-b-line1','precondition':'任意整数','postcondition':'输入',
                                'status':'required_not_guaranteed','evidence':[source()]}]
        self.assertTrue(specification(s,self.reader,{'material:module:1'},node=node('b',2),graph=self.graph))
    def test_config_unknown_needs_explicit_conditional_resolution(self):
        self.graph['discoveries']['a']['unknowns']=[{'description':'实际ABI未知','blocking':True}]
        s=spec();s['sections']['environment']='仅在无符号32位字环境成立'
        r=reviewed()
        self.assertTrue(review(r,self.reader,{'candidate'},node=node('a',1),spec=s,graph=self.graph))
        r['discovery_resolutions']=[{'index':0,'handling':'conditional_scope','condition':'无符号32位字',
                                    'explanation':'只交付明确环境假设下的候选，不认定实际ABI'}]
        self.assertEqual(review(r,self.reader,{'candidate'},node=node('a',1),spec=s,graph=self.graph),[])
        r['discovery_resolutions'][0]['condition']='无符号64位字'
        self.assertTrue(review(r,self.reader,{'candidate'},node=node('a',1),spec=s,graph=self.graph))
    def test_conditional_resolution_does_not_hide_core_unknown(self):
        self.graph['discoveries']['a']['unknowns']=[{'description':'配置未知','blocking':True}]
        s=spec();s['unknowns']=[{'description':'核心结果矛盾','blocking':True}]
        r=reviewed();r['discovery_resolutions']=[{'index':0,'handling':'conditional_scope',
            'condition':s['sections']['environment'],'explanation':'当前只是条件候选'}]
        self.assertTrue(review(r,self.reader,{'candidate'},node=node('a',1),spec=s,graph=self.graph))
    def test_prompt_explicitly_separates_directions_and_safe_ids(self):
        from stage2.prompts import prompt
        text=prompt('write',{})
        self.assertIn('outgoing_edge_ids',text);self.assertIn('caller_scenarios',text)
        self.assertIn('不能用C1',text)
    def test_report_patch_revalidates_and_saves_full_versions(self):
        from stage1.task import run_task
        replies=iter([{'tool':'finish','report':{'ok':False,'large':'x'*3000}},
                      {'tool':'patch_report','changes':{'ok':True}}])
        calls=[]
        def validate(r,reader,reads):
            calls.append(copy.deepcopy(r));return [] if r['ok'] else ['correct ok field']
        result=run_task(self.root,self.base/'patch',lambda m,t:json.dumps(next(replies)),
            'test',validate,role='write',task_id='patch',budgets=Budgets(calls=4,seconds=30,context_chars=20000,reserve_seconds=0),allow_report_patch=True)
        self.assertEqual(result['status'],'task_completed')
        self.assertEqual(len(calls),2);self.assertEqual(result['report']['large'],'x'*3000)
        self.assertEqual(len(list((self.base/'patch/checkpoints').glob('*-report.json'))),2)
        messages=[json.loads(x) for x in (self.base/'patch/conversation.jsonl').read_text().splitlines()]
        assistant=[x for x in messages if x['role']=='assistant']
        self.assertLess(len(assistant[-1]['content']),100)
    def test_patch_cannot_bypass_validator_or_add_fields(self):
        from stage1.task import run_task
        replies=iter([{'tool':'finish','report':{'ok':False}},
                      {'tool':'patch_report','changes':{'invented':True}},
                      {'tool':'patch_report','changes':{'ok':False}}])
        result=run_task(self.root,self.base/'patch-fail',lambda m,t:json.dumps(next(replies)),
            'test',lambda r,reader,reads:['still invalid'],role='write',task_id='patch',
            budgets=Budgets(calls=3,seconds=30,context_chars=20000,reserve_seconds=0,validation_retries=1),allow_report_patch=True)
        self.assertNotEqual(result['status'],'task_completed')
        self.assertEqual(result['validation_failures'],2)
    def test_manifest_traversal_id_and_output_boundary(self):
        m=manifest();m['functions'][0]['id']='../escape'
        with self.assertRaises(ValueError):validate_manifest(m)
        with self.assertRaises(ValueError):run_pipeline(self.root,self.root/'out',manifest(),{'module':'x'},lambda r,t:Model(r,t))


if __name__=='__main__':unittest.main()
