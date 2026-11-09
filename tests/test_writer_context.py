import copy
import json
import unittest
from stage2.context_cards import writer_context,decode_writer_edges
from stage2.required_inputs import plan
from stage2.graph import new_graph


class WriterContextTests(unittest.TestCase):
    def fixture(self):
        node={'id':'f','symbol':'f','source':{'path':'a.c','start':1,'end':9},'configuration':'test','materials':[]}
        graph=new_graph({'functions':[node]})
        for i in range(8):
            graph['edges'][str(i)]={'id':str(i),'caller':'f','callee':None,'callsite':{'path':'a.c','start':i+1,'end':i+1},
                'certainty':'conditional','condition':'DEBUG && WORD_SIZE == 64','unresolved_target':'assert',
                'macro_expansion':{'symbol':'assert','callsite':{'path':'h.h','start':10,'end':10},
                    'condition':'DEBUG && WORD_SIZE == 64','root_call_index':i,'parent_expansion_index':None,
                    'macro_index':0,'declaration_index':None,'unresolved':'external assertion'}}
        return node,graph

    def test_exact_roundtrip_and_graph_unchanged(self):
        node,graph=self.fixture();before=copy.deepcopy(graph)
        view,cards=writer_context(graph,'f')
        self.assertEqual(decode_writer_edges(cards),graph['edges'])
        self.assertEqual(graph,before)
        self.assertNotIn('edges',view);self.assertNotIn('outgoing_edge_ids',view)
        self.assertEqual(len(cards['writer-schema']['shared']['expansions']),1)

    def test_conditions_are_not_merged(self):
        node,graph=self.fixture()
        graph['edges']['1']['macro_expansion']['condition']='!DEBUG'
        _,cards=writer_context(graph,'f')
        self.assertEqual(len(cards['writer-schema']['shared']['expansions']),2)
        self.assertEqual(decode_writer_edges(cards),graph['edges'])

    def test_plan_requires_shared_schema_and_every_relation_page(self):
        node,graph=self.fixture();_,cards=writer_context(graph,'f')
        actions=plan(node,graph,{'source-index':[],**cards})
        ids=[a['id'] for a in actions if a['tool']=='artifact']
        self.assertTrue(set(cards)<=set(ids));self.assertEqual(len(ids),len(set(ids)))

    def test_long_shared_conditions_reduce_relation_size(self):
        node,graph=self.fixture()
        for e in graph['edges'].values():e['condition']='same condition '*80
        _,cards=writer_context(graph,'f')
        self.assertLess(len(json.dumps(cards)),len(json.dumps(graph['edges'])))
