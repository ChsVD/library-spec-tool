"""Stage-four v3 handoff acceptance through the real task/Reader pipeline.

The miniature reference is a fixed fixture, not a Coq or QCP proof. Semantic
review decisions are scripted; these tests check their execution and binding.
"""
import copy
import hashlib
import json
import re
from pathlib import Path
import tempfile
import unittest

from stage1.task import Budgets, write_json
from stage2.graph import digest
from stage2.pipeline import run_pipeline as run_upstream
from stage2.inventory import expand_selection
from stage4 import contracts, planning
from stage4.pipeline import run_pipeline
from tests.test_stage2_inventory import GroupModel, selected


SOURCE = {"path": "lib/code.c", "start": 1, "end": 2}
REFERENCE = {"path": "mini-gmp/empty.v", "start": 1, "end": 2}
MEANING = "mpd_store_Z UINT_MOD ptr n 0 entails n = 0 and emp; the converse is not asserted."


def extraction(ident):
    return {"protocol_version": 3, "function_id": ident,
            "proof_status": "not_proved", "analysis": "Separate representation from caller matching.",
            "needs": [
                {"id": "zero", "function_id": ident, "spec_clause": "n=0 owns no elements",
                 "use_site": "zero-length return", "search_question": "How does mini-GMP represent an empty array?",
                 "source": "spec_extracted", "evidence": [SOURCE]},
                {"id": "caller", "function_id": ident, "spec_clause": "call from emp",
                 "use_site": "caller precondition", "search_question": "Can the target caller construct UInt64Array from emp?",
                 "source": "spec_extracted", "evidence": [SOURCE]}]}


def candidate(ids, mode="correct"):
    refs = [] if mode == "not_found" else [
        {"id": "empty-array", "name": "mpd_store_Z_zero_to_emp", "meaning": MEANING,
         "premises": "mpd_store_Z UINT_MOD ptr n 0: zero size in the reference representation.",
         "evidence": [REFERENCE]}]
    if mode == "reversed":
        refs[0]["meaning"] = "emp entails mpd_store_Z UINT_MOD ptr n 0 for every ptr and n."
    uses = []
    for index, ident in enumerate(ids):
        for need in ("zero", "caller"):
            found = need == "zero" and mode != "not_found"
            uses.append({"id": "f%d-%s" % (index, need), "function_id": ident,
                         "need_id": need, "result": "direct" if found else ("not_found" if mode == "not_found" else "uncertain"),
                         "reference_ids": ["empty-array"] if found else [],
                         "purpose": "Understand empty representation" if found else "Check target caller resource matching",
                         "adaptation": "Preserve elimination direction; target interface remains untested.",
                         "uncertainty": "" if found else "No target caller test establishes construction from emp.",
                         "search_scope": "mini-gmp/empty.v lines 1-2 only",
                         "search_evidence": [REFERENCE], "target_status": "not_validated"})
    if mode == "target_claim":
        uses[1]["purpose"] = "Target caller match has passed."
    return {"protocol_version": 3, "proof_status": "not_proved", "references": refs,
            "uses": uses, "reference_strategies": [], "strategy_search": {
                "reason": "Representation explanation only; no target strategy requested.", "evidence": []},
            "upstream_conditions": {}}


def review(report):
    wrong = any(r["meaning"] != MEANING for r in report["references"])
    claims = [u["id"] for u in report["uses"] if "has passed" in u["purpose"]]
    return {"protocol_version": 3, "proof_status": "not_proved",
            "candidate_digest": planning.candidate_digest(report),
            "verdict": "needs_revision" if wrong or claims else "pass",
            "checks": {key: "Checked original elimination direction and retained target uncertainty." for key in contracts.REFERENCE_CHECKS},
            "reference_reviews": [{"reference_id": r["id"], "verdict": "needs_revision" if wrong else "pass",
                                   "reason": "empty.v:2 eliminates the array; it does not construct it."} for r in report["references"]],
            "use_reviews": [{"use_id": u["id"], "verdict": "needs_revision" if (wrong and u["reference_ids"]) or u["id"] in claims else "pass",
                             "reason": "Direction must match empty.v:2; target caller matching is unvalidated."} for u in report["uses"]],
            "findings": [{"description": "empty.v:2 proves elimination, not construction.", "blocking": True,
                          "reference_ids": ["empty-array"], "use_ids": [u["id"] for u in report["uses"] if u["reference_ids"]]}] if wrong else
                        ([{"description": "No target caller evidence establishes a passed check.", "blocking": True,
                           "reference_ids": [], "use_ids": claims}] if claims else []),
            "evidence": [REFERENCE, SOURCE], "tool_evidence": []}


class FixedReferenceModel:
    def __init__(self, role, mode="correct", seen=None):
        self.role, self.mode, self.seen = role, mode, seen

    def __call__(self, messages, timeout):
        system = messages[0]["content"]
        assignment = json.loads(system.split("任务：\n", 1)[1].split("\n\nTask budgets:")[0])
        ids = json.loads(system.split("Derived artifact IDs: ", 1)[1])
        artifacts, lines = {}, {}
        for message in messages[1:]:
            if message["role"] != "user":
                continue
            try:
                value = json.loads(message["content"])
            except ValueError:
                continue
            if value.get("kind") == "derived_interpretation_not_original_evidence":
                artifacts[value["id"]] = value["content"]
            if value.get("lines"):
                lines.setdefault(value["path"], set()).update(row["line"] for row in value["lines"])
        # Common works from the deterministic need table; full extraction and
        # specification artifacts remain available for a concrete follow-up.
        required_ids = ids
        if self.role == "common" and "needs-summary" in ids:
            required_ids = [ident for ident in ids if ident in (
                "needs-summary", "upstream-context", "specification-writing-guidance",
                "revision_review", "previous_candidate")]
        elif self.role == "review":
            required_ids = [ident for ident in ids if not ident.startswith("extract:")]
        for ident in required_ids:
            if ident not in artifacts:
                return json.dumps({"tool": "artifact", "id": ident, "draft": "Inspect required context."})
        for evidence in (SOURCE, REFERENCE):
            if not set(range(evidence["start"], evidence["end"] + 1)) <= lines.get(evidence["path"], set()):
                return json.dumps({"tool": "read", "path": evidence["path"], "start": evidence["start"],
                                   "count": evidence["end"] - evidence["start"] + 1, "draft": "Read original evidence."})
        if self.seen is not None:
            self.seen.append((self.role, copy.deepcopy(artifacts)))
        if self.role == "extract":
            report = extraction(assignment["function"]["id"])
        elif self.role == "common":
            mode = "correct" if "revision_review" in artifacts else ("reversed" if self.mode == "partial_revision" else self.mode)
            report = candidate(assignment["functions"], mode)
            report["upstream_conditions"] = artifacts.get("upstream-context", {}).get("conditions", {})
            for index, ident in enumerate(assignment["functions"]):
                summary = next((row for row in artifacts.get("needs-summary", {}).get("functions", [])
                                if row["function_id"] == ident), None)
                upstream = (summary["upstream_needs"]["items"] if summary is not None else
                            artifacts["spec:" + ident].get("common_needs", []))
                for n, _ in enumerate(upstream):
                    use = copy.deepcopy(report["uses"][index * 2 + 1])
                    use.update(id="f%d-upstream-%d" % (index, n), need_id="upstream-%d" % n)
                    report["uses"].append(use)
            if mode == "missing_location":
                report["references"][0]["evidence"] = []
            elif mode == "unread_location":
                report["references"][0]["evidence"] = [{**REFERENCE, "start": 3, "end": 3}]
            elif mode == "dangling_reference":
                report["uses"][0]["reference_ids"] = ["absent"]
            elif mode == "target_passed":
                report["uses"][0]["target_status"] = "passed"
            elif mode == "missing_search":
                for use in report["uses"]:
                    use.update(result="not_found", reference_ids=[], search_evidence=[])
                report["references"] = []
        else:
            report = review(artifacts["candidate"])
            if self.mode == "partial_revision" and report["verdict"] == "needs_revision":
                report["verdict"] = "partial"
            report["upstream_condition_checks"] = [
                {"function_id": f, "assumption_id": row["id"], "decision": "preserved",
                 "explanation": "Retained as unvalidated upstream assumption."}
                for f, rows in artifacts.get("upstream-context", {}).get("conditions", {}).items() for row in rows]
            if self.mode == "stale_review":
                report["candidate_digest"] = "0" * 64
            elif self.mode in ("partial_reference", "partial_use"):
                report["verdict"] = "partial"
                affected = ([u["id"] for u in artifacts["candidate"]["uses"] if u["reference_ids"]]
                            if self.mode == "partial_reference" else ["f0-zero"])
                if self.mode == "partial_reference":
                    report["reference_reviews"][0]["verdict"] = "insufficient"
                for use in report["use_reviews"]:
                    if use["use_id"] in affected:
                        use["verdict"] = "insufficient"
                report["findings"] = [{"description": "Applicability is not established for these records.",
                                       "blocking": True, "reference_ids": ["empty-array"] if self.mode == "partial_reference" else [],
                                       "use_ids": affected}]
        return json.dumps({"tool": "finish", "report": report})


class Stage4AcceptanceTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        self.root = self.base / "input"
        (self.root / "lib").mkdir(parents=True)
        (self.root / "mini-gmp").mkdir()
        (self.root / "lib/code.c").write_text("int a(int x) { return b(x); }\nint b(int x) { return x; }\n// end\n")
        (self.root / "mini-gmp/empty.v").write_text(
            "(* fixed miniature reference, not a real proof *)\n"
            "Lemma mpd_store_Z_zero_to_emp : forall ptr n, mpd_store_Z UINT_MOD ptr n 0 |-- “ n = 0 ” && emp.\n"
            "(* intentionally not delivered to these roles *)\n")
        self.upstream = self.base / "upstream"
        self.output = self.base / "common"
        self.budgets = Budgets(calls=24, seconds=30, context_chars=100000, reserve_seconds=0)
        result = run_upstream(self.root, self.upstream, selected(), {"module": "fixture"},
                              lambda role, tid: GroupModel(role, tid), budgets=self.budgets)
        self.assertEqual(result["status"], "candidates_reviewed")

    def run_common(self, mode="correct", **kwargs):
        factory = kwargs.pop("factory", lambda role, tid: FixedReferenceModel(role, mode))
        return run_pipeline(self.root, self.output, self.upstream, factory, budgets=self.budgets, **kwargs)

    def read(self, name):
        return json.loads((self.output / name).read_text())

    def test_reference_and_target_uncertainty_survive_normal_handoff(self):
        seen = []
        result = self.run_common(factory=lambda role, tid: FixedReferenceModel(role, seen=seen))
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        report, reviewed = self.read("candidate.json"), self.read("review.json")
        self.assertEqual(report["protocol_version"], 3)
        self.assertEqual(reviewed["candidate_digest"], planning.candidate_digest(report))
        index = self.read("planning.json")
        self.assertEqual(index["references"], report["references"])
        self.assertEqual(index["uses"], report["uses"])
        self.assertEqual(index["candidate_digest"], reviewed["candidate_digest"])
        self.assertEqual(report["references"][0]["meaning"], MEANING)
        self.assertEqual({u["result"] for u in report["uses"]}, {"direct", "uncertain"})
        self.assertTrue(all(u["target_status"] == "not_validated" for u in report["uses"]))
        self.assertEqual(self.read("reference_strategies/index.json")["strategies"], [])
        markdown = (self.output / "candidate.md").read_text()
        self.assertIn("empty-array", markdown)
        self.assertIn("emp", markdown)
        self.assertEqual({role for role, _ in seen}, {"extract", "common", "review"})
        for role, artifacts in seen:
            guidance = artifacts["specification-writing-guidance"]
            self.assertEqual(guidance["sha256"], hashlib.sha256(guidance["content"].encode()).hexdigest())
            self.assertEqual(guidance["content"], Path(guidance["path"]).read_text())
            if role == "extract":
                self.assertIn("upstream-needs", artifacts)

    def test_default_pipeline_rejects_old_model_reports(self):
        from tests.test_stage3 import Model
        result = self.run_common(factory=lambda role, tid: Model(role))
        self.assertEqual(result["status"], "incomplete", result)
        self.assertFalse((self.output / "candidate.json").exists())

    def test_stage3_cli_with_common_uses_default_v3_pipeline(self):
        from unittest.mock import patch
        from stage3.reference import main
        from tests.test_reference_specs import ReferenceTests
        reference_run = self.base / "reference-cli"
        argv = ["stage3", "--input", str(self.root), "--manifest", "fixture",
                "--output", str(reference_run), "--common-output", str(self.output),
                "--with-common", "--skip-review", "--graph-backend", "lexical"]
        factories = [ReferenceTests().factory([]), lambda role, tid: FixedReferenceModel(role)]
        with patch("sys.argv", argv), patch("stage3.reference.load_manifest",
                  return_value=(expand_selection(self.root, selected()), {})), \
                patch("stage3.reference.model_factory", side_effect=factories), patch("builtins.print"):
            self.assertEqual(main(), 0)
        self.assertEqual(self.read("identity.json")["planning_policy"], 3)
        self.assertEqual(self.read("candidate.json")["protocol_version"], 3)
        self.assertEqual(self.read("status.json")["status"], "common_candidates_reviewed")

    def test_reversed_lemma_is_revised_from_independent_review(self):
        for mode in ("reversed", "partial_revision"):
            with self.subTest(mode=mode):
                self.output = self.base / mode
                seen = []
                result = self.run_common(factory=lambda role, tid: FixedReferenceModel(role, mode, seen))
                self.assertEqual(result["status"], "common_candidates_reviewed", result)
                revisions = [a for role, a in seen if role == "common" and "revision_review" in a]
                self.assertEqual(len(revisions), 1)
                self.assertIn("empty.v:2", revisions[0]["revision_review"]["findings"][0]["description"])
                self.assertEqual(self.read("candidate.json")["references"][0]["meaning"], MEANING)

    def test_target_success_claim_requires_review_revision(self):
        seen = []
        result = self.run_common(factory=lambda role, tid: FixedReferenceModel(role, "target_claim", seen))
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        revisions = [a["revision_review"] for role, a in seen if role == "common" and "revision_review" in a]
        self.assertEqual(len(revisions), 1)
        self.assertEqual(revisions[0]["findings"][0]["use_ids"], ["f0-caller"])
        self.assertTrue(all("has passed" not in u["purpose"] for u in self.read("candidate.json")["uses"]))

    def test_stale_review_cannot_authorize_handoff(self):
        result = self.run_common("stale_review")
        self.assertEqual(result["status"], "incomplete", result)
        self.assertIn("待审", (self.output / "candidate.md").read_text())

    def test_reference_and_use_rejections_have_the_right_scope(self):
        for mode, expected in (("partial_reference", []), ("partial_use", ["f1-zero"])):
            with self.subTest(mode=mode):
                self.output = self.base / mode
                result = self.run_common(mode, max_revisions=0)
                self.assertEqual(result["status"], "partial", result)
                text = (self.output / "candidate.md").read_text()
                approved = "\n".join(re.findall(r"### 可参考清单\n(.*?)(?=###)", text, re.S))
                for ident in ("f0-zero", "f1-zero"):
                    self.assertEqual(ident in approved, ident in expected, approved)

    def test_structural_and_unread_evidence_failures_do_not_publish(self):
        for mode in ("missing_location", "unread_location", "dangling_reference", "target_passed", "missing_search"):
            with self.subTest(mode=mode):
                self.output = self.base / mode
                result = self.run_common(mode)
                self.assertEqual(result["status"], "incomplete", result)
                self.assertFalse((self.output / "candidate.json").exists())
                drafts = [json.loads(p.read_text()) for p in (self.output / "tasks").glob("common-*/draft.json")]
                self.assertTrue(any(d.get("last_feedback", {}).get("validation_errors") for d in drafts),
                                "Concrete validation feedback should be persisted")

    def test_no_matches_can_deliver_with_actual_search_evidence(self):
        result = self.run_common("not_found")
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        report = self.read("candidate.json")
        self.assertEqual(report["references"], [])
        self.assertTrue(all(u["result"] == "not_found" and u["search_evidence"] for u in report["uses"]))

    def test_interruption_resume_clears_current_error_and_retains_history(self):
        class Disconnect:
            def __call__(self, *args, **kwargs):
                raise ConnectionError("acceptance connection interrupted")
        result = self.run_common(factory=lambda role, tid: Disconnect() if role == "review" else FixedReferenceModel(role))
        self.assertEqual(result["status"], "incomplete", result)
        pending = (self.output / "candidate.md").read_text()
        self.assertIn("待审", pending)
        result = self.run_common(resume=True)
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        self.assertEqual(result["run_status"], "completed")
        self.assertFalse(result.get("reason"))
        self.assertTrue(result["error_history"])
        summary = (self.output / "SUMMARY.md").read_text()
        self.assertIn("common_candidates_reviewed", summary)

    def test_old_policy_checkpoint_cannot_inherit_new_review(self):
        self.assertEqual(self.run_common()["status"], "common_candidates_reviewed")
        identity = self.read("identity.json")
        identity["planning_policy"] = 2
        write_json(self.output / "identity.json", identity)
        with self.assertRaisesRegex(ValueError, "policy|protocol|version|changed"):
            self.run_common(resume=True, factory=lambda *args: self.fail("old review cannot be reused"))

    def test_optional_upstream_needs_preserve_presence_and_original_items(self):
        graph = json.loads((self.upstream / "graph.json").read_text())
        rows = list(graph["nodes"].values())
        rows[0]["spec"].pop("common_needs", None)
        rows[1]["spec"]["common_needs"] = []
        write_json(self.upstream / "graph.json", graph)
        status = json.loads((self.upstream / "status.json").read_text())
        status["graph_digest"] = digest(graph)
        write_json(self.upstream / "status.json", status)
        result = self.run_common()
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        for row, present in zip(rows, (False, True)):
            report = self.read("functions/" + row["id"] + "/common_needs.json")
            self.assertEqual(report["upstream_needs"]["present"], present)
            self.assertEqual(report["upstream_needs"]["items"], [])
            self.assertEqual(len(report["needs"]), 2)

    def test_nonempty_upstream_needs_keep_original_identity(self):
        graph = json.loads((self.upstream / "graph.json").read_text())
        ident = next(iter(graph["nodes"]))
        original = [{"name": "caller empty resource", "purpose": "Check construction from emp",
                     "status": "needed_not_proved"}]
        graph["nodes"][ident]["spec"]["common_needs"] = original
        write_json(self.upstream / "graph.json", graph)
        status = json.loads((self.upstream / "status.json").read_text())
        status["graph_digest"] = digest(graph)
        write_json(self.upstream / "status.json", status)
        result = self.run_common()
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        needs = self.read("functions/" + ident + "/common_needs.json")
        self.assertEqual(needs["upstream_needs"], {"present": True, "items": original, "ids": ["upstream-0"]})
        matching = [u for u in self.read("candidate.json")["uses"] if u["function_id"] == ident and u["need_id"] == "upstream-0"]
        self.assertEqual(len(matching), 1)


if __name__ == "__main__":
    unittest.main()
