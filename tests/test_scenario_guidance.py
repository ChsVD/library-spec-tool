import copy
import json
from pathlib import Path
import tempfile
import unittest
from stage3.scenario_guidance import load_catalog, validate_scenarios
from stage3.reference import run
from stage2.inventory import expand_selection
from tests.scenario_fixture import scenario

class ScenarioGuidanceTests(unittest.TestCase):
    def test_multidomain_and_custom_focus_without_predefined_answer(self):
        catalog=load_catalog()
        a=scenario({"writing_guidance":catalog})
        a["selected_domains"]=["integer_array","concurrency"]
        a["focus"] += [
            {"topic":"integer_array.aliasing","basis":"Shared buffer call","application":"Keep alias conditions unknown pending evidence","status":"unknown"},
            {"topic":"concurrency.interference","basis":"Lock in supplied source","application":"Describe ownership during lock hold","status":"applicable"},
            {"topic":"custom.device_order","basis":"Device-specific task","application":"Record environment ordering uncertainty","status":"unknown"}]
        a["unknowns"]=["No evidence for current QCP matching"]
        validate_scenarios([{"scenario_analysis":a}],catalog)
        a["selected_domains"].append("invented_domain")
        with self.assertRaisesRegex(ValueError,"catalog IDs"):
            validate_scenarios([{"scenario_analysis":a}],catalog)

    def test_missing_analysis_or_missing_general_requirement_rejected(self):
        catalog=load_catalog()
        with self.assertRaisesRegex(ValueError,"scenario_analysis"):
            validate_scenarios([{}],catalog)
        a=scenario({"writing_guidance":catalog});a["focus"].pop()
        with self.assertRaisesRegex(ValueError,"general requirements"):
            validate_scenarios([{"scenario_analysis":a}],catalog)

    def test_unselected_domain_and_duplicate_topics_rejected(self):
        catalog=load_catalog();a=scenario({"writing_guidance":catalog})
        a["focus"].append({**a["focus"][0],"topic":"numerical.error"})
        with self.assertRaisesRegex(ValueError,"unknown scenario topic"):
            validate_scenarios([{"scenario_analysis":a}],catalog)
        a["focus"][-1]=copy.deepcopy(a["focus"][0])
        with self.assertRaisesRegex(ValueError,"duplicate"):
            validate_scenarios([{"scenario_analysis":a}],catalog)

    def test_catalog_edit_and_reserved_ids(self):
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/"catalog.json";c=load_catalog()
            c["domains"][0]["id"]="general";p.write_text(json.dumps(c))
            with self.assertRaisesRegex(ValueError,"reserved"):
                load_catalog(p)

    def test_generation_uses_snapshot_and_changed_catalog_blocks_resume(self):
        with tempfile.TemporaryDirectory() as tmp:
            base=Path(tmp);root=base/"input";root.mkdir()
            (root/"a.c").write_text("int f(int x){return x;}")
            manifest=expand_selection(root,{"version":2,"scope_decision":"fixture","materials":{},
                "selection":{"id":"m","module_id":"m","kind":"module","paths":["a.c"],"configuration":"test","materials":[]}})
            p=base/"catalog.json";c=load_catalog()
            c["domains"].append({"id":"project_local","title":"Local domain","when_relevant":"Fixture",
                                 "points":[{"id":"local","guidance":"Explicit project requirement"}]})
            p.write_text(json.dumps(c))
            calls=[]
            def factory(ident):
                def model(messages,timeout):
                    a=json.loads(messages[1]["content"]);calls.append(a)
                    rows=[{"function_id":n["id"],"scenario_analysis":scenario(a),
                           "observations":"identity","suggested_spec":"ret=x","assumptions":"fixture",
                           "callee_requirements":[]} for n in a["assigned"]]
                    return json.dumps({"tool":"finish","report":{"functions":rows}})
                return model
            kwargs=dict(review=False,graph_backend="lexical",domain_catalog=p)
            g=run(root,base/"out",manifest,{},factory,**kwargs)
            self.assertEqual(len(calls),1) # No extra analysis/review model session.
            self.assertEqual(calls[0]["writing_guidance"],c)
            self.assertEqual(json.loads((base/"out/writing-guidance.json").read_text()),c)
            self.assertIn("scenario_analysis",next(iter(g["nodes"].values()))["spec"])
            self.assertTrue(list((base/"out/tasks").rglob("generated-scenarios.json")))
            self.assertTrue(list((base/"out/tasks").rglob("final-scenarios.json")))
            run(root,base/"out",manifest,{},factory,resume=True,**kwargs)
            self.assertEqual(len(calls),1)
            c["general_requirements"][0]["guidance"]+=" changed"
            p.write_text(json.dumps(c))
            with self.assertRaisesRegex(ValueError,"resume identity changed"):
                run(root,base/"out",manifest,{},factory,resume=True,**kwargs)
