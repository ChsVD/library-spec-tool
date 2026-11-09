import copy
import json
import unittest
from stage4 import contracts, planning
from tests import test_stage3 as fixtures


class PlanningTests(unittest.TestCase):
    setUp = fixtures.Stage3Tests.setUp
    tearDown = fixtures.Stage3Tests.tearDown

    def validate(self, report):
        return contracts.candidate(report, self.reader, self.reads,
                                   nodes=self.nodes, extracts=self.extracts)

    def reference(self):
        return {"id":"existing","name":"identity","search_scope":"lib/code.c only",
                "applicability":"scalar identity",
                "facets":{k:{"status":"read" if k=="definition" else "not_applicable",
                             "reason":"source definition" if k=="definition" else "no relevance for this scalar fixture",
                             "evidence":[{"path":"lib/code.c","start":1,"end":3}] if k=="definition" else []}
                          for k in planning.FACETS}}

    def test_reuse_tracks_read_reference_without_new_definition(self):
        r=fixtures.proposal(self.ids);r["references"]=[self.reference()]
        r["items"][0].update(origin="source_fact",evidence=[{"path":"lib/code.c","start":1,"end":3}])
        for row in r["coverage"].values():
            row["needs"][0].update(action="reuse",reference_ids=["existing"])
        self.assertEqual(self.validate(r),[])
        r["references"][0]["facets"]["definition"]["status"]="not_found"
        self.assertIn("selected reuse definition must be read",self.validate(r))

    def test_unread_reference_and_missing_read_facets_rejected(self):
        r=fixtures.proposal(self.ids);r["references"]=[self.reference()]
        r["references"][0]["facets"]["definition"]["evidence"][0]["end"]=99
        self.assertTrue(self.validate(r))
        del r["references"][0]["facets"]["boundaries"]
        self.assertTrue(self.validate(r))

    def test_no_common_content_is_valid_and_unknown_is_not_review_pass(self):
        r=fixtures.proposal(self.ids);r["items"]=[]
        for row in r["coverage"].values():
            row.pop("categories")
            row["needs"][0].update(action="not_needed",item_ids=[],explanation="Inline equality already states requirement")
        self.assertEqual(self.validate(r),[])
        self.assertEqual(contracts.review(fixtures.review(),self.reader,self.reads|{"candidate"},proposal=r,nodes=self.nodes),[])
        r["coverage"][self.ids[0]]["needs"][0].update(action="unknown",unresolved="representation not determined")
        self.assertEqual(self.validate(r),[])
        self.assertTrue(contracts.review(fixtures.review(),self.reader,self.reads|{"candidate"},proposal=r,nodes=self.nodes))

    def test_malformed_reference_facets_return_diagnostics(self):
        for bad in (None, [], {"definition":None}):
            r=fixtures.proposal(self.ids);ref=self.reference();ref["facets"]=bad;r["references"]=[ref]
            for row in r["coverage"].values():
                row["needs"][0].update(action="reuse",reference_ids=["existing"])
            self.assertTrue(self.validate(r))

    def test_planning_cannot_claim_executed_validation(self):
        for status in ("passed","failed","executed","proved"):
            r=fixtures.proposal(self.ids)
            r["items"][0]["validation_obligations"][0]["status"]=status
            self.assertTrue(self.validate(r))
        r=fixtures.proposal(self.ids)
        r["items"][0]["validation_obligations"]=[]
        self.assertTrue(self.validate(r))

    def test_custom_domain_and_requirement_trace(self):
        r=fixtures.extract(self.ids[0]);r.pop("categories")
        r["needs"][0].update(name="protocol transition",spec_clause="Ensure state=Closed",
                             use_site="successful close branch",scope="local")
        self.assertEqual(contracts.extraction(r,self.reader,{"spec"},node=self.nodes[self.ids[0]]),[])
        del r["needs"][0]["spec_clause"]
        self.assertTrue(contracts.extraction(r,self.reader,{"spec"},node=self.nodes[self.ids[0]]))
        r=fixtures.extract(self.ids[0]);r["categories"]=None
        self.assertTrue(contracts.extraction(r,self.reader,{"spec"},node=self.nodes[self.ids[0]]))

    def test_snapshot_and_policy_prevent_old_resume(self):
        output=self.base/"common"
        result=fixtures.run_pipeline(self.root,output,self.upstream,lambda r,t:fixtures.Model(r),budgets=self.budgets)
        self.assertEqual(result["status"],"common_candidates_reviewed")
        plan=json.loads((output/"planning.json").read_text())
        self.assertEqual(plan["candidate_digest"],fixtures.digest(json.loads((output/"candidate.json").read_text())))
        self.assertEqual(plan["execution_status"],"not_started")
        self.assertEqual(set(plan["needs"]),set(self.ids))
        path=output/"identity.json";identity=json.loads(path.read_text());identity.pop("planning_policy")
        path.write_text(json.dumps(identity))
        with self.assertRaisesRegex(ValueError,"planning policy"):
            fixtures.run_pipeline(self.root,output,self.upstream,lambda *args:None,resume=True)
