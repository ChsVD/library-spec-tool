from tests.scenario_fixture import scenario
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from stage1.task import write_json
from stage2.inventory import expand_selection
from stage3.reference import run, validate_scoped, bind_requirements
from stage3.reference_review import REVIEW_PROMPT, approved
from stage2.demand_scope import create_plan, load_plan, plan_graph, project, _plan_graph_v1
from stage2.graph import digest
from stage4.pipeline import load_upstream
from tests.test_reference_review import review_row


class DemandScopeTests(unittest.TestCase):
    def setUp(self):
        tmp=tempfile.TemporaryDirectory();self.addCleanup(tmp.cleanup)
        self.base=Path(tmp.name);self.root=self.base/"input";self.root.mkdir()
        (self.root/"a.c").write_text(
            "int aux(void){return 1;}\nint t1(void){return 1;}\nint t2(void){return 2;}\n"
            "int left(void){return t1();}\nint right(void){return t1()+t2();}\n"
            "int top(void){return left()+right()+aux();}\nint other(void){return t1();}\n"
            "int unused(void){return 0;}\nint a(void){return b();}\nint b(void){return a()+t2();}\n")
        self.manifest=expand_selection(self.root,{"version":2,"scope_decision":"fixture",
            "materials":{},"selection":{"id":"group","module_id":"m","kind":"module",
            "paths":["a.c"],"configuration":"test","materials":[]}})
        self.source=self.base/"source"
        self.graph=run(self.root,self.source,self.manifest,{},prepare_only=True,graph_backend="lexical")
        self.ids={n["symbol"]:i for i,n in self.graph["nodes"].items()}
        self.calls=[]

    def make_plan(self, targets=("t1","t2"), roots=None):
        plan,_=create_plan(self.root,self.source,[self.ids[x] for x in targets],
                           [self.ids[x] for x in roots] if roots is not None else None)
        path=self.base/"plan.json";write_json(path,plan)
        return plan,path

    def factory(self,ident):
        def model(messages,timeout):
            a=json.loads(messages[1]["content"])
            role="review" if messages[0]["content"]==REVIEW_PROMPT else "write"
            self.calls.append((role,a))
            if role=="review":
                rows=[review_row(n["id"]) for n in a["assigned"]]
            else:
                rows=[]
                for n in a["assigned"]:
                    req=[]
                    for e in a["outgoing"]+a.get("boundary_edges",[]):
                        if e["caller"]==n["id"]:
                            req.append({"edge_id":e["id"],"callee_id":e["callee"],"callee":e["symbol"],
                                "callsite_indices":list(range(len(e["callsites"]))),
                                "condition":"Fixture call domain; configuration unverified","requirement":"Return the specified value"})
                    rows.append({"function_id":n["id"],"scenario_analysis":scenario(a),"observations":"Fixture implementation",
                                 "suggested_spec":"With entry state; Require resources; Ensure exact output",
                                 "assumptions":"Static scope is incomplete","callee_requirements":req})
            return json.dumps({"tool":"finish","report":{"functions":rows}})
        return model

    def execute(self,plan,path,**kwargs):
        return run(self.root,self.base/"out",self.manifest,{},self.factory,
                   scope_plan=path,approve_scope=plan["plan_digest"],**kwargs)

    def test_union_deduplicates_ancestors_and_retains_auxiliary_boundary(self):
        plan,path=self.make_plan()
        self.assertEqual(set(plan["target_ids"]),{self.ids["t1"],self.ids["t2"]})
        self.assertEqual(len(plan["generation_ids"]),len(set(plan["generation_ids"])))
        self.assertIn(self.ids["top"],plan["demand_ids"])
        self.assertIn(self.ids["other"],plan["demand_ids"])
        self.assertIn(self.ids["aux"],plan["context_ids"])
        self.assertNotIn(self.ids["unused"],plan["generation_ids"])
        _,g=load_plan(self.root,path,self.manifest)
        self.assertEqual(g["boundary_nodes"][self.ids["aux"]]["role"],"context")
        self.assertTrue(any(e["callee"]==self.ids["aux"] for e in g["boundary_edges"]))
        self.assertFalse(any(e["callee"]==self.ids["aux"] for e in g["edges"].values()))

    def test_explicit_roots_keep_all_paths_and_record_omitted_callers(self):
        plan,_=self.make_plan(roots=("top",))
        self.assertTrue({self.ids["left"],self.ids["right"]}<=set(plan["demand_ids"]))
        self.assertIn(self.ids["other"],plan["excluded_ancestor_ids"])
        self.assertIn(self.ids["other"],plan["context_ids"])
        self.assertTrue(plan["excluded_incoming_edge_ids"])
        with self.assertRaisesRegex(ValueError,"every target SCC"):
            self.make_plan(roots=("left",))
        with self.assertRaisesRegex(ValueError,"each requested root"):
            self.make_plan(roots=("unused",))

    def test_scc_target_expansion(self):
        plan,_=self.make_plan(targets=("a","t1"))
        self.assertIn(self.ids["b"],plan["scc_added_target_ids"])
        g=project(self.graph,plan)
        self.assertEqual(g["nodes"][self.ids["b"]]["role"],"target")
        self.assertTrue(any(set(c["members"])=={self.ids["a"],self.ids["b"]} for c in g["components"]))

    def test_exact_ids_required(self):
        with self.assertRaisesRegex(ValueError,"exact function IDs"):
            plan_graph(self.graph,["t1","t2"])
        with self.assertRaises(ValueError):
            plan_graph(self.graph,[self.ids["t1"],self.ids["t1"]])

    def test_plan_mutation_source_mutation_and_input_mutation_rejected(self):
        plan,path=self.make_plan()
        changed=copy.deepcopy(plan);changed["target_ids"]=[]
        write_json(path,changed)
        with self.assertRaisesRegex(ValueError,"digest"):
            load_plan(self.root,path,self.manifest)
        # Even a rehashed edit must match the computed scope.
        changed["plan_digest"]=digest({k:v for k,v in changed.items() if k!="plan_digest"})
        write_json(path,changed)
        with self.assertRaisesRegex(ValueError,"recomputed"):
            load_plan(self.root,path,self.manifest)
        write_json(path,plan)
        changed_graph=copy.deepcopy(self.graph);changed_graph["unknown_calls"].append({"caller":self.ids["t1"],"reason":"new"})
        write_json(self.source/"graph.json",changed_graph)
        with self.assertRaisesRegex(ValueError,"graph/status"):
            load_plan(self.root,path,self.manifest)
        write_json(self.source/"graph.json",self.graph)
        (self.root/"a.c").write_text("int changed(void){return 0;}")
        with self.assertRaisesRegex(ValueError,"snapshot"):
            load_plan(self.root,path,self.manifest)

    def test_prepare_only_and_approval_before_model(self):
        plan,path=self.make_plan()
        with patch("stage3.reference.build_graph",side_effect=AssertionError("must not rebuild")):
            run(self.root,self.base/"out",self.manifest,{},scope_plan=path,prepare_only=True)
            with self.assertRaisesRegex(ValueError,"approve-scope"):
                run(self.root,self.base/"out",self.manifest,{},self.factory,scope_plan=path,resume=True)
            self.assertEqual(self.calls,[])
            g=self.execute(plan,path,resume=True)
        self.assertTrue(all(approved(n) for n in g["nodes"].values()))
        writes=[n["id"] for role,a in self.calls if role=="write" for n in a["assigned"]]
        self.assertEqual(sorted(writes),plan["generation_ids"])
        before=len(self.calls);self.execute(plan,path,resume=True);self.assertEqual(before,len(self.calls))
        target_assignment=next(a for role,a in self.calls if role=="write" and any(n["id"]==self.ids["t1"] for n in a["assigned"]))
        self.assertEqual(len(target_assignment["incoming"]),3)
        self.assertTrue(all(e["requirements"] for e in target_assignment["incoming"]))

    def test_target_only_stage3_handoff_and_boundary_background(self):
        plan,path=self.make_plan(roots=("top",))
        self.execute(plan,path)
        graph,nodes,_=load_upstream(self.root,self.base/"out")
        self.assertEqual(set(nodes),set(plan["target_ids"]))
        self.assertEqual({n["id"] for n in graph["upstream_context"]["demand_context"]},set(plan["demand_ids"]))
        self.assertTrue(graph["upstream_context"]["boundary_edges"])
        self.assertTrue(graph["upstream_context"]["semantic_review"])
        self.assertFalse(graph["upstream_context"]["proved"])
        status=json.loads((self.base/"out/status.json").read_text());status["scope_approved"]=False
        write_json(self.base/"out/status.json",status)
        with self.assertRaisesRegex(ValueError,"approval"):
            load_upstream(self.root,self.base/"out")

    def test_requirements_bind_exact_edges_and_call_sites(self):
        plan,_=self.make_plan(roots=("top",));g=project(self.graph,plan)
        edge=next(e for e in g["edges"].values() if e["caller"]==self.ids["right"] and e["callee"]==self.ids["t1"])
        record={"function_id":self.ids["right"],"observations":"x","suggested_spec":"x","assumptions":"x",
                "callee_requirements":[{"edge_id":edge["id"],"callee_id":edge["callee"],"callee":edge["symbol"],
                                       "callsite_indices":[0],"condition":"x","requirement":"x"}]}
        validate_scoped({"functions":[record]},[record["function_id"]],g)
        bind_requirements(g,record["function_id"],record["callee_requirements"])
        self.assertTrue(g["edges"][edge["id"]]["requirements"])
        self.assertTrue(all(not e["requirements"] for e in g["edges"].values() if e["id"]!=edge["id"]))
        bad=copy.deepcopy(record);bad["callee_requirements"][0]["callee_id"]=self.ids["t2"]
        with self.assertRaisesRegex(ValueError,"exact outgoing"):
            validate_scoped({"functions":[bad]},[bad["function_id"]],g)
        bad=copy.deepcopy(record);bad["callee_requirements"][0]["callsite_indices"]=[99]
        with self.assertRaisesRegex(ValueError,"callsite_indices"):
            validate_scoped({"functions":[bad]},[bad["function_id"]],g)


    def test_same_named_callees_do_not_share_edge_requirements(self):
        plan,_=self.make_plan(roots=("top",));g=project(self.graph,plan)
        edges=[e for e in g["edges"].values() if e["caller"]==self.ids["right"]]
        self.assertEqual(len(edges),2)
        for e in edges:
            e["symbol"]="same"
            g["nodes"][e["callee"]]["symbol"]="same"
        chosen=edges[0]
        requirement={"edge_id":chosen["id"],"callee_id":chosen["callee"],"callee":"same",
                     "callsite_indices":[0],"condition":"first implementation","requirement":"specific requirement"}
        bind_requirements(g,self.ids["right"],[requirement])
        self.assertEqual(chosen["requirements"],[requirement])
        self.assertEqual(edges[1]["requirements"],[])

    def test_high_target_closes_dependencies_and_hands_all_to_stage3(self):
        plan,path=self.make_plan(targets=("top",), roots=("top",))
        wanted={self.ids[x] for x in ("top","left","right","aux","t1","t2")}
        self.assertEqual(set(plan["target_ids"]),wanted)
        self.assertEqual(set(plan["dependency_added_target_ids"]),wanted-{self.ids["top"]})
        self.assertEqual(plan["demand_ids"],[])
        self.execute(plan,path)
        graph,nodes,_=load_upstream(self.root,self.base/"out")
        self.assertEqual(set(nodes),wanted)
        self.assertEqual(graph["upstream_context"]["dependency_scope"]["requested_target_ids"],
                         [self.ids["top"]])
        writes=[n["id"] for role,a in self.calls if role=="write" for n in a["assigned"]]
        self.assertLess(writes.index(self.ids["top"]),writes.index(self.ids["t1"]))
        order={i:k for k,c in enumerate(plan["proof_order_components"]) for i in c}
        for edge in self.graph["edges"].values():
            if edge["caller"] in wanted and edge["callee"] in wanted:
                self.assertLess(order[edge["callee"]],order[edge["caller"]])

    def test_added_dependency_collects_other_callers_demands(self):
        plan,_=self.make_plan(targets=("left",))
        self.assertEqual(set(plan["target_ids"]),{self.ids["left"],self.ids["t1"]})
        self.assertIn(self.ids["other"],plan["demand_ids"])
        self.assertIn(self.ids["right"],plan["demand_ids"])
        # A demand-only caller's unrelated callee is still a declared boundary.
        self.assertNotIn(self.ids["t2"],plan["target_ids"])
        self.assertIn(self.ids["t2"],plan["context_ids"])

    def test_recursive_dependency_is_indivisible_and_old_draft_is_not_a_stop(self):
        graph=copy.deepcopy(self.graph)
        graph["nodes"][self.ids["t2"]].update(status="reference_draft",spec={"old":"draft"})
        plan=plan_graph(graph,[self.ids["a"]])
        self.assertEqual(set(plan["target_ids"]),{self.ids[x] for x in ("a","b","t2")})
        self.assertIn(self.ids["t2"],plan["dependency_added_target_ids"])
        self.assertTrue(any(set(c)=={self.ids["a"],self.ids["b"]}
                            for c in plan["proof_order_components"]))
        self.assertIsNone(project(graph,plan)["nodes"][self.ids["t2"]]["spec"])

    def test_explicit_dependency_boundary_preserves_shared_other_path(self):
        boundary=[{"function_id":self.ids["left"],"reason":"Separate work; contract applicability pending"}]
        plan,graph=create_plan(self.root,self.source,[self.ids["top"]],[self.ids["top"]],boundary)
        self.assertNotIn(self.ids["left"],plan["generation_ids"])
        self.assertIn(self.ids["t1"],plan["target_ids"])  # still reached through right
        self.assertIn(self.ids["left"],plan["context_ids"])
        self.assertEqual(plan["dependency_status"],"unresolved")
        path=self.base/"boundary.json";write_json(path,plan)
        _,projected=load_plan(self.root,path,self.manifest)
        self.assertTrue(any(u.get("boundary_callee")==self.ids["left"]
                            for u in projected["unknown_calls"]))
        self.execute(plan,path)
        loaded,_,_=load_upstream(self.root,self.base/"out")
        self.assertEqual(loaded["upstream_context"]["dependency_scope"]["dependency_boundaries"],boundary)

    def test_invalid_boundaries_and_scc_cuts_rejected(self):
        for boundaries in [
            [{"function_id":self.ids["b"],"reason":"cannot cut target SCC"}],
            [{"function_id":self.ids["unused"],"reason":"unreachable"}],
            [{"function_id":self.ids["t2"],"reason":""}],
            [{"function_id":"t2","reason":"bare name"}],
        ]:
            with self.subTest(boundaries=boundaries),self.assertRaises(ValueError):
                plan_graph(self.graph,[self.ids["a"]],dependency_boundaries=boundaries)

    def test_unknown_callee_is_not_a_verified_leaf(self):
        graph=copy.deepcopy(self.graph)
        unknown={"caller":self.ids["t1"],"reason":"unresolved function pointer"}
        graph["unknown_calls"].append(unknown)
        plan=plan_graph(graph,[self.ids["left"]],[self.ids["left"]])
        self.assertIn(unknown,plan["target_unknown_calls"])
        self.assertEqual(plan["dependency_status"],"unresolved")
        self.assertIn(unknown,project(graph,plan)["unknown_calls"])

    def test_v1_plan_keeps_historical_scope(self):
        plan=_plan_graph_v1(self.graph,[self.ids["top"]],[self.ids["top"]])
        identity=json.loads((self.source/"identity.json").read_text())
        plan.update(source_run=str(self.source.resolve()),source_graph_digest=digest(self.graph),
                    input_snapshot_digest=digest(identity["input_snapshot"]),
                    source_manifest_digest=digest(self.manifest))
        plan["plan_digest"]=digest(plan)
        path=self.base/"legacy.json";write_json(path,plan)
        loaded,g=load_plan(self.root,path,self.manifest)
        self.assertEqual(loaded["version"],1)
        self.assertEqual(set(g["nodes"]),{self.ids["top"]})
        self.execute(plan,path)
        _,nodes,_=load_upstream(self.root,self.base/"out")
        self.assertEqual(set(nodes),{self.ids["top"]})
