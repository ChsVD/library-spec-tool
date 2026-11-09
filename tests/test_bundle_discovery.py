import copy
import unittest
from stage2.bundled import replace_discovery

class ReplacementTests(unittest.TestCase):
    def test_replacement_removes_old_edges_and_invalidates_neighbors(self):
        nodes={k:{'status':'reviewed_candidate'} for k in ('a','b','c')}
        def edge(i,a,b):
            return {'id':i,'caller':a,'callee':b,'callsite':{},'condition':'always','certainty':'conditional'}
        old=edge('a-call-0','a','b'); incoming=edge('c-call-0','c','a')
        graph={'nodes':nodes,'edges':{old['id']:old,incoming['id']:incoming},'discoveries':{'a':{'old':True}}}
        report={'function_id':'a','neighbors':[],'edges':[edge('a-call-0','a','c')]}
        replace_discovery(graph,report)
        self.assertEqual(graph['edges']['a-call-0']['callee'],'c')
        self.assertEqual(graph['edges']['c-call-0'],incoming)
        self.assertTrue(all(n['status']=='needs_recheck' for n in graph['nodes'].values()))
        replace_discovery(graph,dict(report,edges=[]))
        self.assertEqual(set(graph['edges']),{'c-call-0'})

    def test_invalid_replacement_is_atomic(self):
        graph={'nodes':{},'edges':{},'discoveries':{}}
        before=copy.deepcopy(graph)
        with self.assertRaises(ValueError):
            replace_discovery(graph,{'function_id':'a','neighbors':[],'edges':[{'caller':'b'}]})
        self.assertEqual(graph,before)
