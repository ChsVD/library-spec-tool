import json
import tempfile
import unittest
from pathlib import Path
from stage1.task import Budgets
from stage2.inventory import expand_selection
from stage3.reference import run
from stage2.selection_tools import ScopeTools, Limits, SelectionReader
from stage2.select import run_selection, validate
from stage2.demand_scope import load_plan


class SelectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.root = self.base/"input"
        self.root.mkdir()
        (self.root/"README.md").write_text("A sample arithmetic library.\n")
        (self.root/"a.c").write_text(
            "int leaf(void){return 1;}\n"
            "int other(void){return 2;}\n"
            "int middle(void){return leaf();}\n"
            "int top(void){return middle()+other();}\n"
            "int mystery(void){return unresolved();}\n"
            "int a(void){return b();}\n"
            "int b(void){return a();}\n")
        self.manifest=expand_selection(self.root,{"version":2,"scope_decision":"fixture","materials":{},
            "selection":{"id":"m","module_id":"m","kind":"module","paths":["a.c"],"configuration":"test","materials":[]}})
        self.source=self.base/"graph"
        self.graph=run(self.root,self.source,self.manifest,{},prepare_only=True,graph_backend="lexical")
        self.ids={n["symbol"]:i for i,n in self.graph["nodes"].items()}
        self.tools=ScopeTools(self.root,self.graph)

    def test_shared_dependencies_are_counted_once_and_increment_is_static(self):
        t=self.tools.evaluate([self.ids["top"]],[self.ids["middle"]])
        self.assertEqual(t["new_target_count"],2)
        self.assertEqual(t["new_dependency_count"],1)
        self.assertEqual(t["counts"]["targets"],4)

    def test_demand_callers_are_included_in_material_budget(self):
        t=self.tools.evaluate([self.ids["leaf"]])
        self.assertEqual(t["counts"]["targets"],1)
        self.assertEqual(t["counts"]["demand_callers"],2)
        small=ScopeTools(self.root,self.graph,Limits(max_generation=2))
        self.assertIn("generation",small.evaluate([self.ids["leaf"]])["exceeded"])

    def test_recursive_group_and_unknown_leaf_are_not_lost(self):
        frontier=self.tools.frontier()["items"]
        recursive=next(r for r in frontier if self.ids["a"] in [n["id"] for n in r["members"]])
        self.assertEqual({n["id"] for n in recursive["members"]},{self.ids["a"],self.ids["b"]})
        mystery=next(r for r in frontier if self.ids["mystery"] in [n["id"] for n in r["members"]])
        self.assertGreater(mystery["unknown_call_count"],0)
        self.assertEqual(self.tools.evaluate([self.ids["mystery"]])["material_status"],"unknown")

    def test_missing_source_blocks_feasibility(self):
        (self.root/"a.c").unlink()
        t=self.tools.evaluate([self.ids["leaf"]])
        self.assertFalse(t["within_limits"])
        self.assertGreater(t["missing_source_count"],0)

    def test_graph_queries_do_not_grant_source_evidence(self):
        reader=SelectionReader(self.root,self.base/"reads.jsonl",self.tools)
        value=reader.execute({"tool":"evaluate_group","target_ids":[self.ids["leaf"]]})
        self.assertTrue(value["within_limits"])
        self.assertEqual(reader.reads,{})
        report={"outcome":"selected","target_ids":[self.ids["leaf"]],
                "assessment_id":value["assessment_id"],"reason":"useful","stop_reason":"small",
                "evidence":[{"path":"README.md","start":1,"end":1},{"path":"a.c","start":1,"end":1}]}
        self.assertTrue(validate(report,reader,set(),self.tools,["README.md"]))

    def test_caps_and_invalid_ids_are_not_model_overridable(self):
        tools=ScopeTools(self.root,self.graph,Limits(max_targets=1,max_material_chars=1))
        value=tools.evaluate([self.ids["top"]])
        self.assertFalse(value["within_limits"])
        self.assertIn("targets",value["exceeded"])
        self.assertIn("known_material_chars",value["exceeded"])
        with self.assertRaises(ValueError):
            tools.evaluate(["top"])
        with self.assertRaises(ValueError):
            Limits(max_targets=0)

    def test_single_session_produces_loadable_unapproved_scope(self):
        # A fixture model only: no external model or proof invocation.
        assessment=self.tools.evaluate([self.ids["middle"]])
        actions=iter([
            {"tool":"read","path":"a.c","start":3,"count":1},
            {"tool":"evaluate_group","target_ids":[self.ids["middle"]]},
            {"tool":"finish","report":{"outcome":"selected","target_ids":[self.ids["middle"]],
                "assessment_id":assessment["assessment_id"],"reason":"A small usable operation.",
                "stop_reason":"Stop before top; its other dependency increases the batch.",
                "evidence":[{"path":"README.md","start":1,"end":1},{"path":"a.c","start":3,"end":3}]}}
        ])
        result=run_selection(self.root,self.source,self.base/"selection",["README.md"],
            lambda messages,timeout:json.dumps(next(actions)),
            budgets=Budgets(calls=8,seconds=60,context_chars=60000,reserve_seconds=0))
        self.assertEqual(result["status"],"pending_user_review")
        self.assertFalse(result["user_approved"])
        plan,_=load_plan(self.root,self.base/"selection/scope-plan.json",self.manifest)
        self.assertEqual(set(plan["target_ids"]),{self.ids["middle"],self.ids["leaf"]})
        self.assertTrue((self.base/"selection/assessment.json").exists())
        self.assertFalse((self.base/"selection/specs").exists())

    def test_source_change_during_selection_rejects_publication(self):
        def model(messages,timeout):
            (self.root/"README.md").write_text("changed")
            return json.dumps({"tool":"finish","report":{"outcome":"unable","target_ids":[],
                "reason":"Not enough context","stop_reason":"stop",
                "evidence":[{"path":"README.md","start":1,"end":1}]}})
        # Read evidence changes are rejected before any selected plan can be published.
        result=run_selection(self.root,self.source,self.base/"changed",["README.md"],model,
            budgets=Budgets(calls=2,seconds=60,context_chars=60000,reserve_seconds=0))
        self.assertNotEqual(result["status"],"pending_user_review")
        self.assertFalse((self.base/"changed/scope-plan.json").exists())
