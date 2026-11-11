import json
import unittest
from pathlib import Path
from tests import test_stage3 as fixtures
Model=fixtures.Model
from stage4.pipeline import run_pipeline
from stage1.evidence_completion import plan
from stage1.reader import Reader

class RecoveryTests(unittest.TestCase):
    setUp=fixtures.Stage3Tests.setUp
    tearDown=fixtures.Stage3Tests.tearDown

    def execute(self, out, factory, **kwargs):
        return run_pipeline(self.root,self.base/out,self.upstream,factory,budgets=self.budgets,protocol_version=2,**kwargs)

    def test_length_revalidate_without_common_regeneration(self):
        result=self.execute("failed",lambda r,t:Model(r),max_report_chars=2000)
        self.assertEqual(result["status"],"incomplete")
        original=(self.base/"failed/checkpoint.json").read_bytes()
        calls=[]
        class Spy(Model):
            def __call__(self,messages,timeout):
                calls.append(self.role)
                return super().__call__(messages,timeout)
        result=self.execute("fixed",lambda r,t:Spy(r),max_report_chars=10000,recover_from=self.base/"failed")
        self.assertEqual(result["status"],"common_candidates_reviewed",result)
        self.assertNotIn("extract",calls)
        self.assertNotIn("common",calls)
        self.assertIn("review",calls)
        self.assertEqual((self.base/"failed/checkpoint.json").read_bytes(),original)
        self.assertTrue((self.base/"fixed/reference_strategies/index.json").exists())

    def test_coverage_repair_keeps_full_validation_and_review(self):
        class Missing(Model):
            def __call__(self,messages,timeout):
                action=json.loads(super().__call__(messages,timeout))
                if self.role=="common" and action.get("tool")=="finish":
                    next(iter(action["report"]["coverage"].values()))["needs"]=[]
                return json.dumps(action)
        result=self.execute("bad",lambda r,t:Missing(r))
        self.assertEqual(result["status"],"incomplete")
        roles=[]
        def factory(r,t):
            roles.append(r)
            return Model(r)
        result=self.execute("repaired",factory,recover_from=self.base/"bad")
        self.assertEqual(result["status"],"common_candidates_reviewed",result)
        self.assertNotIn("extract",roles)
        self.assertIn("common",roles)
        self.assertIn("review",roles)

    def test_model_identity_change_rejected(self):
        self.execute("badmodel",lambda r,t:Model(r),max_report_chars=2000)
        with self.assertRaisesRegex(ValueError,"changed input"):
            self.execute("newmodel",lambda r,t:Model(r),recover_from=self.base/"badmodel",
                         max_report_chars=10000,model_identity={"model":"different"})

    def test_original_completion_only_reads_missing_lines(self):
        reader=Reader(self.root,self.base/"completion.jsonl")
        reader.execute({"tool":"read","path":"lib/code.c","start":1,"count":1})
        actions,missing=plan({"evidence":[{"path":"lib/code.c","start":1,"end":3}]},reader)
        self.assertEqual(missing,[])
        self.assertEqual(actions,[{"tool":"read","path":"lib/code.c","start":2,"count":2}])
        self.assertEqual(len(reader.reads["lib/code.c"]),1)

    def test_malformed_json_preserved_then_repaired(self):
        class Malformed(Model):
            def __init__(self,role):super().__init__(role);self.first=True
            def __call__(self,messages,timeout):
                if self.role=="common" and self.first:
                    self.first=False
                    return '{"tool": "finish", broken}'
                return super().__call__(messages,timeout)
        result=self.execute("format",lambda r,t:Malformed(r))
        self.assertEqual(result["status"],"common_candidates_reviewed",result)
        raw=list((self.base/"format/tasks").glob("common-*/raw-response-1.txt"))
        self.assertEqual(len(raw),1)
        self.assertEqual(raw[0].read_text(),'{"tool": "finish", broken}')
