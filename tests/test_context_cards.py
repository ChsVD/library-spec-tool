import copy
import json
import unittest
from stage2.context_cards import source_index, source_cards, compact_context, ranges
from stage2.graph import new_graph, merge_discovery
from stage2.bundled import discovery_from_report, required_details

class ContextCardsTests(unittest.TestCase):
    def fixture(self):
        node={'id':'f','symbol':'f','configuration':'C','source':{'path':'f.c','start':1,'end':2}}
        macro={'kind':'macro','symbol':'M','source':{'path':'h.h','start':1,'end':4},'condition':'DEBUG','reason':'long explanation'*100}
        root={'symbol':'M','target_id':None,'declaration_index':0,'callsite':node['source'],'condition':'DEBUG','unresolved':''}
        exp={'symbol':'g','target_id':None,'declaration_index':None,'callsite':{'path':'h.h','start':2,'end':2},'condition':'DEBUG and x','unresolved':'missing declaration'*100,'root_call_index':0,'parent_expansion_index':None,'macro_index':0}
        report={'function_id':'f','snippets':[macro],'calls':[root],'macro_expansions':[exp],
                'coverage':dict(types='unknown',macros='unknown',declarations='unknown'),
                'unknowns':[{'description':'Missing original interface'*100,'blocking':True}]}
        m={'report':report,'configuration':'C','mappings':[{'original':x} for x in [node['source'],macro['source'],macro['source'],{'path':'h.h','start':6,'end':6}]]}
        graph=new_graph({'functions':[node]});merge_discovery(graph,discovery_from_report(node,report,{}))
        return node,m,graph
    def test_index_is_navigation_not_repeated_expansion_report(self):
        _,m,_=self.fixture();index=source_index([(None,m)])[0]
        self.assertNotIn('macro_expansions',index);self.assertNotIn('unknowns',index)
        self.assertLess(len(json.dumps(index)),700)
        self.assertEqual(len(index['ranges']),3) # duplicate removed; uncopied line 5 stays a gap
        self.assertEqual(index['blocking_unknown_count'],1)
    def test_compact_projection_preserves_full_graph_and_lossless_details(self):
        _,m,g=self.fixture();original=copy.deepcopy(g)
        view,cards=compact_context(g,'f')
        self.assertEqual(g,original)
        self.assertNotIn('macro_expansion',view['edges'][1])
        detail=cards[view['edges'][1]['detail']][view['edges'][1]['id']]
        self.assertEqual(detail['macro_expansion'],g['edges']['f-call-1']['macro_expansion'])
        self.assertEqual(cards[view['unknowns'][0]['detail']]['0'],g['discoveries']['f']['unknowns'][0])
        self.assertLess(len(json.dumps(view)),len(json.dumps(g)))
    def test_definitions_are_shared_between_function_packages(self):
        _,m,_=self.fixture();other=copy.deepcopy(m);other['report']['function_id']='other'
        cards=source_cards([(None,m),(None,other)])
        self.assertEqual(len([k for k in cards if k.startswith('macro:')]),1)
        self.assertEqual(cards['bundle:f']['macro_definitions'][0]['detail'],cards['bundle:other']['macro_definitions'][0]['detail'])

    def test_navigation_alone_is_not_detail_read_credit(self):
        _,_,g=self.fixture();view,cards=compact_context(g,'f')
        self.assertTrue(required_details(g,'f',{'source-index'}))
        self.assertEqual(required_details(g,'f',set(cards)),[])
