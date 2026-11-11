import copy,json,shutil,unittest
from pathlib import Path
from tests import test_stage3 as fixtures
from stage1.runner import snapshot
from stage4.pipeline import run_pipeline
from stage4.components import validate
from stage4.input_revision import transition

class RevisionTests(unittest.TestCase):
    setUp=fixtures.Stage3Tests.setUp
    tearDown=fixtures.Stage3Tests.tearDown

    def setup_transition(self):
        class Insufficient(fixtures.Model):
            def __call__(self,messages,timeout):
                a=json.loads(super().__call__(messages,timeout))
                if self.role=="review" and a.get("tool")=="finish":
                    a["report"]["verdict"]="insufficient"
                    a["report"]["findings"]=[{"description":"Need foundation","blocking":True}]
                return json.dumps(a)
        result=run_pipeline(self.root,self.base/"seed",self.upstream,lambda r,t:Insufficient(r),budgets=self.budgets,protocol_version=2)
        self.assertEqual(result["status"],"insufficient")
        root=self.base/"newinput";shutil.copytree(self.root,root)
        (root/"foundation").mkdir();(root/"foundation/base.v").write_text("Definition base := 1.\n")
        added=[{**r,"origin":"test foundation"} for r in snapshot(root) if r["path"]=="foundation/base.v"]
        manifest={"version":1,"baseline_root":str(self.root),"new_root":str(root),
                  "source_stage3_run":str(self.upstream),"added_files":added}
        path=self.base/"transition.json";path.write_text(json.dumps(manifest))
        return root,path

    def test_added_material_delivered_and_full_review_repeated(self):
        root,path=self.setup_transition();seen=[];roles=[]
        class Revised(fixtures.Model):
            def __call__(self,messages,timeout):
                if any('"path": "foundation/base.v"' in m["content"] and '"lines"' in m["content"] for m in messages):
                    seen.append(self.role)
                a=json.loads(super().__call__(messages,timeout))
                if self.role=="review" and a.get("tool")=="finish":
                    a["report"]["item_reviews"]=[{"item_id":"identity","verdict":"pass","reason":"checked",
                                                   "action":"retain","material_needed":""}]
                return json.dumps(a)
        def factory(r,t):roles.append(r);return Revised(r)
        result=run_pipeline(root,self.base/"revised",self.upstream,factory,budgets=self.budgets,protocol_version=2,
                            component_review=True,input_transition=path,revise_from=self.base/"seed")
        self.assertEqual(result["status"],"common_candidates_reviewed",result)
        self.assertEqual(roles,["common","review"])
        self.assertIn("common",seen);self.assertIn("review",seen)
        self.assertTrue((self.base/"revised/reference_strategies/index.json").exists())
        self.assertEqual(json.loads((self.base/"seed/status.json").read_text())["status"],"insufficient")

    def test_transition_rejects_modified_or_unlisted_files(self):
        root,path=self.setup_transition()
        (root/"extra.txt").write_text("not authorized")
        with self.assertRaisesRegex(ValueError,"allowlist"):
            transition(root,self.upstream,snapshot(self.root),path)
        (root/"extra.txt").unlink();(root/"lib/code.c").write_text("changed")
        with self.assertRaisesRegex(ValueError,"modified"):
            transition(root,self.upstream,snapshot(self.root),path)

    def test_partial_dependencies_and_blockers(self):
        proposal={"items":[{"id":"math","depends_on":[]},{"id":"memory","depends_on":[]}],
                  "unknowns":[],"coverage":{}}
        report={"verdict":"partial","findings":[],"item_reviews":[
            {"item_id":"math","verdict":"pass","reason":"checked","action":"retain"},
            {"item_id":"memory","verdict":"insufficient","reason":"need definitions",
             "action":"add_material","material_needed":"array predicate"}]}
        self.assertEqual(validate(report,proposal),[])
        proposal["items"][0]["depends_on"]=["memory"]
        self.assertTrue(validate(report,proposal))
        proposal["items"][0]["depends_on"]=[]
        proposal["unknowns"]=[{"blocking":True}]
        self.assertTrue(validate(report,proposal))
        proposal["unknowns"][0]["item_ids"]=["memory"]
        self.assertEqual(validate(report,proposal),[])
        report["verdict"]="pass"
        self.assertTrue(validate(report,proposal))
