import copy
import json
from pathlib import Path
import tempfile
import unittest
from stage1.task import Budgets
from stage2.inventory import scan_c, expand_selection, validate_selection_manifest, progress
from stage2.graph import new_graph
from stage2.pipeline import run_pipeline, load_manifest
from stage2.contracts import discovery
from tests.test_stage2 import Model, spec, reviewed


def selected(paths=None,kind='function_group'):
    return {'version':2,'scope_decision':'process the entire selected source group','materials':{'module':{}},
            'selection':{'id':'arithmetic','module_id':'math','kind':kind,
                         'paths':paths or ['lib/code.c'],'configuration':'generic conditional model',
                         'materials':['module'],'exclude_files':[]}}


class GroupModel(Model):
    def __call__(self,messages,timeout):
        result=json.loads(super().__call__(messages,timeout))
        if result.get('tool')!='finish':return json.dumps(result)
        system=messages[0]['content'];a=json.loads(system.split('任务：\n',1)[1].split('\n\nTask budgets:')[0])
        node=a['function'];ident=node['id']
        if self.role=='discover':
            by_symbol={n['symbol']:n for n in a['known_same_file'].values()}
            e={'id':'a-b-line1','caller':by_symbol['a']['id'],'callee':by_symbol['b']['id'],
               'certainty':'direct','condition':'always','callsite':{'path':'lib/code.c','start':1,'end':1}}
            r={'function_id':ident,'neighbors':[],'edges':[e] if node['symbol'] in ('a','b') else [],
               'coverage':{'outgoing':'checked_scope','incoming':'fixture file only'},'unknowns':[]}
        elif self.role=='write':
            r=spec(ident);r['claims'][0]['evidence']=[node['source']]
            r['call_requirements']=spec('a')['call_requirements'] if node['symbol']=='a' else []
        else:
            r=reviewed(ident);r['evidence']=[node['source']]
        return json.dumps({'tool':'finish','report':r},ensure_ascii=False)


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.base=Path(self.tmp.name);self.root=self.base/'input'
        (self.root/'lib').mkdir(parents=True)
        (self.root/'lib/code.c').write_text('int a(int x) { return b(x); }\nint b(int x) { return x; }\nint unrelated(int x) { return x+1; }\n')
    def tearDown(self):self.tmp.cleanup()
    def test_group_expands_all_definitions_including_disconnected(self):
        m=expand_selection(self.root,selected())
        self.assertEqual([n['symbol'] for n in m['functions']],['a','b','unrelated'])
        self.assertEqual(len(set(n['id'] for n in m['functions'])),3)
        g=new_graph(m);p=progress(g)
        self.assertEqual(p['expected_count'],3);self.assertEqual(p['reviewed_count'],0)
        self.assertFalse(p['all_selected_complete'])
    def test_directory_scope_includes_multiple_files_and_static_functions(self):
        (self.root/'lib/extra.c').write_text('static int helper(void) { return 1; }\n')
        m=expand_selection(self.root,selected(['lib'],kind='module'))
        self.assertEqual(len(m['functions']),4)
        self.assertIn('helper',[n['symbol'] for n in m['functions']])
    def test_scanner_ignores_comments_strings_prototypes_and_macros(self):
        text='/* int fake(void) { return 0; } */\n#define FAKE(x) { x; }\nint prototype(void);\nstruct S { int field; };\nint real(int (*callback)(int)) {\n const char *s = "} fake() {";\n return callback(2);\n}\n'
        entries,gaps=scan_c(text,'sample.c')
        self.assertEqual([n['symbol'] for n in entries],['real']);self.assertEqual(gaps,[])
        self.assertEqual(entries[0]['source'],{'path':'sample.c','start':5,'end':8})
    def test_macro_generated_definition_cannot_silently_disappear(self):
        entries,gaps=scan_c('MAKE_FUNCTION(hidden);\nint visible(void) {return 0;}\n','sample.c')
        self.assertEqual([e['symbol'] for e in entries],['visible'])
        self.assertTrue(gaps)
        _,gaps=scan_c('MAKE_FUNCTION(hidden)\n','sample.c');self.assertTrue(gaps)
    def test_conditional_definitions_keep_distinct_identities(self):
        (self.root/'lib/code.c').write_text('#if WORD64\nint same(void) {return 64;}\n#else\nint same(void) {return 32;}\n#endif\n')
        m=expand_selection(self.root,selected());nodes=m['functions']
        self.assertEqual(len(nodes),2);self.assertNotEqual(nodes[0]['id'],nodes[1]['id'])
        self.assertIn('#if WORD64',nodes[0]['configuration']);self.assertIn('#else',nodes[1]['configuration'])
    def test_unparsed_body_is_a_gap_not_silent_omission(self):
        (self.root/'lib/code.c').write_text('DEFINE_FUNCTION(foo) { return 1; }\nint ok(void) { return 0; }\n')
        m=expand_selection(self.root,selected());self.assertTrue(m['selection_inventory']['gaps'])
        self.assertEqual(m['selection_inventory']['scope_status'],'needs_scope_review')
        self.assertFalse(progress(new_graph(m))['all_selected_complete'])
    def test_unsupported_assembly_requires_explicit_scope_decision(self):
        (self.root/'lib/asm.S').write_text('assembly')
        m=expand_selection(self.root,selected(['lib'],kind='module'))
        self.assertTrue(m['selection_inventory']['gaps'])
        s=selected(['lib'],kind='module');s['selection']['exclude_files']=[{'path':'lib/asm.S','reason':'C function group only; assembly is deferred'}]
        m=expand_selection(self.root,s);self.assertEqual(m['selection_inventory']['gaps'],[])
        self.assertEqual(next(f for f in m['selection_inventory']['files'] if f['path'].endswith('.S'))['status'],'excluded')
    def test_single_function_cannot_disguise_as_group(self):
        (self.root/'lib/code.c').write_text('int a(void) {return 0;}\n')
        m=expand_selection(self.root,selected())
        self.assertEqual(m['selection_inventory']['scope_status'],'needs_scope_review')
    def test_missing_selected_node_prevents_group_completion(self):
        g=new_graph(expand_selection(self.root,selected()))
        first=next(iter(g['nodes']));g['nodes'][first]['status']='reviewed_candidate'
        self.assertFalse(progress(g)['all_selected_complete'])
        del g['nodes'][first]
        self.assertEqual(progress(g)['missing_function_ids'],[first])
    def test_batch_size_one_processes_entire_group(self):
        result=run_pipeline(self.root,self.base/'run',selected(),{'module':'fixture module'},lambda r,t:GroupModel(r,t),
            budgets=Budgets(calls=16,seconds=30,context_chars=60000,reserve_seconds=0),batch_size=1)
        self.assertEqual(result['status'],'candidates_reviewed',result)
        self.assertEqual(result['selection_progress']['expected_count'],3)
        self.assertEqual(result['selection_progress']['reviewed_count'],3)
        self.assertEqual(len(result['functions']),3)
    def test_partial_failure_retains_group_pending(self):
        def factory(r,t):return GroupModel(r,t,fail=r=='write' and 'unrelated-' in t)
        result=run_pipeline(self.root,self.base/'run',selected(),{'module':'fixture'},factory,
            budgets=Budgets(calls=16,seconds=30,context_chars=60000,reserve_seconds=0),batch_size=1)
        self.assertEqual(result['status'],'incomplete')
        self.assertEqual(result['selection_progress']['reviewed_count'],2)
        self.assertEqual(len(result['selection_progress']['pending_function_ids']),1)
        resumed=run_pipeline(self.root,self.base/'run',selected(),{'module':'fixture'},lambda r,t:GroupModel(r,t),
            budgets=Budgets(calls=16,seconds=30,context_chars=60000,reserve_seconds=0),resume=True)
        self.assertEqual(resumed['status'],'candidates_reviewed',resumed)
        self.assertEqual(resumed['selection_progress']['reviewed_count'],3)
    def test_inventory_gap_stops_before_model_calls(self):
        (self.root/'lib/bad.c').write_text('DEFINE_FUNCTION(foo) { return 1; }\n')
        result=run_pipeline(self.root,self.base/'run',selected(['lib']),{'module':'fixture'},lambda r,t:self.fail('must not call model'))
        self.assertEqual(result['status'],'needs_scope_review')
        self.assertEqual(result['selection_progress']['expected_count'],3)
    def test_empty_or_fully_unparsed_group_stays_incomplete(self):
        (self.root/'lib/code.c').write_text('DEFINE_FUNCTION(foo) {return 0;}\n')
        result=run_pipeline(self.root,self.base/'run',selected(),{'module':'fixture'},lambda r,t:self.fail('must not call model'))
        self.assertEqual(result['status'],'needs_scope_review')
        self.assertFalse(result['selection_progress']['all_selected_complete'])
    def test_real_bn_word_inventory_has_five_functions(self):
        root=Path(__file__).resolve().parent.parent/'input'
        if not (root/'openssl/crypto/bn/bn_word.c').exists():self.skipTest('local source copy unavailable')
        m=expand_selection(root,selected(['openssl/crypto/bn/bn_word.c']))
        self.assertEqual([n['symbol'] for n in m['functions']],['BN_mod_word','BN_div_word','BN_add_word','BN_sub_word','BN_mul_word'])
        self.assertEqual(m['selection_inventory']['gaps'],[])
    def test_input_escape_and_function_whitelist_rejected(self):
        with self.assertRaises(ValueError):expand_selection(self.root,selected(['../outside']))
        m=selected();m['functions']=[]
        with self.assertRaises(ValueError):validate_selection_manifest(m)
    def test_duplicate_neighbor_cannot_hide_selected_definition(self):
        from stage1.reader import Reader
        m=expand_selection(self.root,selected());g=new_graph(m);a,b,_=m['functions']
        reader=Reader(self.root,self.base/'reads');reader.execute({'tool':'read','path':'lib/code.c','count':3})
        r={'function_id':a['id'],'neighbors':[{**b,'id':'duplicate-b'}],'edges':[],
           'coverage':{'outgoing':'checked_scope','incoming':'fixture'},'unknowns':[]}
        errors=discovery(r,reader,set(),node=a,known=g['nodes'])
        self.assertTrue(any('canonical ID' in e for e in errors))


if __name__=='__main__':unittest.main()
