import tempfile
import unittest
from pathlib import Path
from stage2.inventory import expand_selection
from stage2.frontier import plan

class FrontierTests(unittest.TestCase):
    def build(self, files, kind='module'):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup);root=Path(tmp.name)
        for name,text in files.items():(root/name).write_text(text)
        m={'version':2,'scope_decision':'whole module','materials':{},'selection':{'id':'m','module_id':'m','kind':kind,'paths':['.'],'configuration':'test','materials':[]}}
        return root,expand_selection(root,m)

    def test_cross_file_leaf_and_blocked_caller(self):
        root,m=self.build({'word.c':'int upper(void) { return lower(); }','asm.c':'int lower(void) { return 1; }'})
        r=plan(root,m);by={n['symbol']:n for n in r['functions']}
        self.assertEqual(by['lower']['status'],'candidate_for_review')
        self.assertEqual(by['upper']['status'],'blocked_dependencies')
        self.assertEqual(by['upper']['dependencies'][0]['candidate_ids'],[by['lower']['id']])
        self.assertEqual(r['proof_ready_ids'],[])

    def test_macro_indirect_external_and_recursion_not_ready(self):
        root,m=self.build({'a.c':'#define WRAP(x) ext(x)\nint a(void) { return WRAP(1); }\nint b(void) { return external(); }\nint c(void) { return c(); }\nint d(void) { return (*fp)(); }'})
        r=plan(root,m)
        self.assertTrue(all(n['status']!='candidate_for_review' for n in r['functions']))

    def test_conditional_variants_retained(self):
        root,m=self.build({'a.c':'#ifdef X\nint leaf(void) {return 1;}\n#else\nint leaf(void) {return 2;}\n#endif\nint caller(void) {return leaf();}'})
        r=plan(root,m);self.assertEqual(len(r['functions']),3)
        caller=next(n for n in r['functions'] if n['symbol']=='caller')
        self.assertEqual(caller['dependencies'][0]['state'],'ambiguous_definition')
        self.assertEqual(r['recommended_ids'],[])

    def test_file_group_rejected(self):
        root,m=self.build({'a.c':'int a(void){return 0;} int b(void){return 1;}'},kind='function_group')
        with self.assertRaises(ValueError):plan(root,m)

    def test_inventory_gap_not_silently_ready(self):
        root,m=self.build({'a.c':'GENERATE(foo);\nint leaf(void){return 0;}'})
        r=plan(root,m);self.assertTrue(r['inventory_gaps']);self.assertEqual(r['recommended_ids'],[])

    def test_return_cast_not_a_call(self):
        root,m=self.build({'a.c':'unsigned long leaf(void){return (unsigned long)0;}'})
        r=plan(root,m);self.assertEqual(r['functions'][0]['dependencies'],[])

    def test_processed_contract_configuration_must_match(self):
        root,m=self.build({'a.c':'int a(void){return ext();}'})
        c={'symbol':'ext','configuration':'other'}
        self.assertEqual(plan(root,m,[c])['functions'][0]['status'],'blocked_dependencies')
        c['configuration']='test'
        self.assertEqual(plan(root,m,[c])['functions'][0]['dependencies'][0]['state'],'processed_interface')
