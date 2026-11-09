import copy
import tempfile
import unittest
from pathlib import Path
from stage1.reader import Reader
from stage2.source_bundle import merge_extraction, validate_extraction, materialize
from stage2.bundled import discovery_from_report, expansion_evidence, source_index
from stage2.context_cards import source_cards

class Supplements(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.base=Path(self.tmp.name);self.root=self.base/'input';self.root.mkdir()
        (self.root/'a.c').write_text('int f(int x) { CHECK(x); return x; }\n')
        (self.root/'a.h').write_text('#define CHECK(x) INNER(x)\n#define INNER(x) g(x)\nint g(int x);\nstruct value { int capacity; };\n#define WIDTH 32\n')
        self.node={'id':'f','symbol':'f','source':{'path':'a.c','start':1,'end':1},'configuration':'test'}
        self.reader=Reader(self.root,self.base/'reads')
        for path in ('a.c','a.h'):self.reader.execute({'tool':'read','path':path})
        def snippet(kind,symbol,line):return {'kind':kind,'symbol':symbol,'source':{'path':'a.h','start':line,'end':line},'reason':'dependency','condition':'always'}
        self.snippets=[snippet('macro','CHECK',1),snippet('macro','INNER',2),snippet('declaration','g',3)]
        def call(symbol,di,path,line):return {'symbol':symbol,'declaration_index':di,'callsite':{'path':path,'start':line,'end':line},'condition':'always','unresolved':'','target_id':None}
        self.report={'function_id':'f','snippets':self.snippets,'calls':[call('CHECK',0,'a.c',1)],
          'macro_expansions':[dict(call('INNER',1,'a.h',1),root_call_index=0,parent_expansion_index=None,macro_index=0),dict(call('g',2,'a.h',2),root_call_index=0,parent_expansion_index=0,macro_index=1)],
          'coverage':dict(types='checked',macros='checked',declarations='checked'),'unknowns':[]}
        self.struct=snippet('type','value',4);self.width=snippet('macro','WIDTH',5)
    def validate(self,r):return validate_extraction(r,self.reader,{},node=self.node,selected={'f':self.node})
    def test_nested_macro_dependencies_and_graph_provenance(self):
        self.assertEqual(self.validate(self.report),[])
        d=discovery_from_report(self.node,self.report,{})
        self.assertEqual(len(d['edges']),3)
        e=d['edges'][2]
        self.assertEqual(e['callsite'],self.node['source'])
        self.assertEqual(e['macro_expansion']['callsite']['path'],'a.h')
        graph={'edges':{e['id']:e}}
        self.assertEqual(expansion_evidence(graph,'f',self.reader),[])
        self.reader.reads.clear()
        self.assertTrue(expansion_evidence(graph,'f',self.reader))
    def test_header_call_not_accepted_as_lexical_call(self):
        r=copy.deepcopy(self.report);r['calls'][0]['callsite']['path']='a.h'
        self.assertTrue(any('target implementation' in x for x in self.validate(r)))
    def test_wrong_parent_and_cycles_rejected(self):
        for key,value in [('parent_expansion_index',1),('macro_index',2),('root_call_index',3)]:
            r=copy.deepcopy(self.report);r['macro_expansions'][1][key]=value
            self.assertTrue(self.validate(r))
        r=copy.deepcopy(self.report);r['macro_expansions'][1]['callsite']['start']=3;r['macro_expansions'][1]['callsite']['end']=3
        self.assertTrue(any('within parent macro' in x for x in self.validate(r)))
    def test_macro_single_symbol_explicit_error(self):
        r=copy.deepcopy(self.report);r['snippets'][0]['symbol']='CHECK, INNER'
        self.assertTrue(any('one C identifier' in x for x in self.validate(r)))
    def test_supplement_retains_structure_and_remaps_indices(self):
        old=copy.deepcopy(self.report);old['snippets'].insert(0,self.struct)
        # No old call indices are used: the current complete dependency assessment replaces them.
        new=copy.deepcopy(self.report);new['snippets'].append(self.width)
        before=copy.deepcopy(old)
        merged=merge_extraction(old,new)
        self.assertEqual(old,before)
        self.assertEqual(merged['snippets'][0],self.struct)
        self.assertEqual(merged['calls'][0]['declaration_index'],1)
        self.assertEqual(merged['macro_expansions'][1]['macro_index'],2)
        self.assertEqual(self.validate(merged),[])
        m=materialize(self.root,self.base/'pack',self.node,merged)
        header=(self.base/'pack/dependencies.h').read_text()
        self.assertIn('struct value',header);self.assertIn('#define WIDTH',header)
        self.assertEqual(len(m['report']['macro_expansions']),2)
        index=source_index([(self.base/'pack',m)])[0]
        self.assertNotIn('macro_roots',index)
        cards=source_cards([(self.base/'pack',m)])
        self.assertEqual(cards[index['details']]['macro_definitions'][0]['index'],1)
    def test_metadata_conflict_does_not_modify_previous(self):
        old=copy.deepcopy(self.report);new=copy.deepcopy(old);new['snippets'][0]['condition']='OTHER_CONFIG'
        before=copy.deepcopy(old)
        with self.assertRaisesRegex(ValueError,'conflicting'):merge_extraction(old,new)
        self.assertEqual(old,before)
    def test_unresolved_expansion_requires_blocking_unknown(self):
        r=copy.deepcopy(self.report);r['macro_expansions'][1].update(declaration_index=None,unresolved='missing g prototype')
        self.assertTrue(self.validate(r))
        r['unknowns']=[{'description':'g prototype missing','blocking':True}]
        self.assertEqual(self.validate(r),[])

    def test_wide_macro_context_cannot_hide_wrong_owner(self):
        r=copy.deepcopy(self.report)
        r['snippets'][0]['source']['end']=2
        r['macro_expansions'][0]['callsite'].update(start=2,end=2)
        self.assertTrue(any('named macro body' in x for x in self.validate(r)))
