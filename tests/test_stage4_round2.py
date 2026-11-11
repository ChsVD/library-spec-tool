"""Offline real-entry acceptance fixture, reusable against both material policies.

The source is deliberately synthetic. Scripted semantic decisions are not proofs.
``run_fixture(Path(...), bundled=False)`` returns the status and all model requests;
copy this file into an old checkout to measure that checkout's actual delivery.
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from stage1.task import Budgets, write_json
from stage1.reader import Reader
from stage2.graph import digest
from stage2.pipeline import run_pipeline as run_upstream
from stage2.source_bundle import materialize
from stage4 import contracts, planning
from stage4.pipeline import run_pipeline
from tests.test_stage2_inventory import GroupModel, selected


LEMMA = {"path": "reference/model.v", "start": 1, "end": 3}
BOUNDARY = {"path": "reference/model.v", "start": 4, "end": 5}
BACKGROUND = {"path": "background.txt", "start": 1, "end": 30}
EXTRA = "SECOND_FUNCTION_ONLY: x must fit in the target signed integer range."
BUDGETS = Budgets(calls=24, seconds=30, context_chars=100000, reserve_seconds=0)


def delivered(messages):
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
    return artifacts, lines


class Round2Model:
    def __init__(self, role, tid, requests):
        self.role, self.tid, self.requests = role, tid, requests
        self.overlap_requested = False

    def __call__(self, messages, timeout):
        self.requests.append({"role": self.role, "tid": self.tid, "messages": copy.deepcopy(messages)})
        system = messages[0]["content"]
        assignment = json.JSONDecoder().raw_decode(system.split("任务：\n", 1)[1])[0]
        artifacts, lines = delivered(messages)
        action = lambda value: json.dumps(value, ensure_ascii=False)
        read = lambda src: action({"tool": "read", "path": src["path"], "start": src["start"],
                                  "count": src["end"] - src["start"] + 1, "draft": "Inspect original source."})
        if self.role == "extract":
            node = assignment["function"]
            for src in (node["source"], BACKGROUND):
                if not set(range(src["start"], src["end"] + 1)) <= lines.get(src["path"], set()):
                    return read(src)
            report = {"protocol_version": 3, "function_id": node["id"], "proof_status": "not_proved",
                      "analysis": "Identity relation; background was inspected but does not support the recommendation.",
                      "needs": [{"id": "identity", "function_id": node["id"], "spec_clause": "return equals x",
                                 "use_site": "return expression", "search_question": "Find the shared identity lemma and its domain.",
                                 "source": "spec_extracted", "evidence": [node["source"], BACKGROUND]}]}
            return action({"tool": "finish", "report": report})
        if not set(range(1, 4)) <= lines.get(LEMMA["path"], set()):
            return read(LEMMA)
        # Deliberately overlaps the lemma and the candidate's boundary citation.
        # Both checkouts receive the same request; only actual tool delivery differs.
        if not self.overlap_requested:
            self.overlap_requested = True
            return read({"path": LEMMA["path"], "start": 2, "end": 6})
        if self.role == "common":
            ids = assignment["functions"]
            conditions = {ids[1]: [{"id": "signed-range", "condition": EXTRA}]}
            report = {"protocol_version": 3, "proof_status": "not_proved",
                      "references": [{"id": "identity", "name": "identity_value", "meaning": "identity_value x = x",
                                      "premises": "Mathematical integers; target signed range is separate.", "evidence": [LEMMA]}],
                      "uses": [{"id": "use-" + ident, "function_id": ident, "need_id": "identity", "result": "adapt",
                                "reference_ids": ["identity"], "purpose": "Describe the returned input value.",
                                "adaptation": EXTRA if index == 1 else "No additional function-specific condition.",
                                "uncertainty": "Target QCP use remains unvalidated.", "search_scope": "reference/model.v:1-6",
                                "search_evidence": [LEMMA, BOUNDARY], "target_status": "not_validated"}
                               for index, ident in enumerate(ids)],
                      "reference_strategies": [], "strategy_search": {"reason": "No relevant existing strategy needed.", "evidence": []},
                      "upstream_conditions": conditions}
        else:
            candidate = artifacts["candidate"]
            report = {"protocol_version": 3, "proof_status": "not_proved", "verdict": "pass",
                      "candidate_digest": planning.candidate_digest(candidate),
                      "checks": {key: "Read shared lemma and boundary definition independently; preserve the second function condition."
                                 for key in contracts.REFERENCE_CHECKS},
                      "reference_reviews": [{"reference_id": "identity", "verdict": "pass", "reason": "Original equality and domain checked."}],
                      "use_reviews": [{"use_id": use["id"], "verdict": "pass", "reason": "Function-specific applicability condition retained."}
                                      for use in candidate["uses"]],
                      "upstream_condition_checks": [{"function_id": ident, "assumption_id": row["id"], "decision": "preserved",
                                                     "explanation": "The original condition remains an assumption."}
                                                    for ident, rows in candidate["upstream_conditions"].items() for row in rows],
                      "findings": [], "evidence": [LEMMA, BOUNDARY], "tool_evidence": []}
        return action({"tool": "finish", "report": report})


def run_fixture(base, bundled=False):
    """Build one fixed upstream, invoke the real stage-four entry, retain requests."""
    root, upstream, output = base / "input", base / "upstream", base / "common"
    (root / "lib").mkdir(parents=True)
    (root / "reference").mkdir()
    (root / "lib/code.c").write_text("int a(int x) { return b(x); }\nint b(int x) { return x; }\n// end\n")
    (root / "background.txt").write_text("".join("UNRELATED_BACKGROUND_%02d: historical commentary without applicable facts.\n" % i for i in range(30)))
    (root / "reference/model.v").write_text(
        "(* synthetic reference fixture, not a compiled proof *)\nDefinition identity_value (x : Z) := x.\n"
        "Lemma identity_value_eq : forall x, identity_value x = x.\nDefinition target_min := -2147483648.\n"
        "Definition target_max := 2147483647.\n(* boundary definitions require independent inspection *)\n")
    result = run_upstream(root, upstream, selected(), {"module": "fixture"},
                          lambda role, tid: GroupModel(role, tid), budgets=BUDGETS)
    if result["status"] != "candidates_reviewed":
        raise AssertionError(result)
    graph = json.loads((upstream / "graph.json").read_text())
    nodes = list(graph["nodes"].values())
    nodes[1]["spec"]["conditional_assumptions"] = [{"id": "signed-range", "condition": EXTRA}]
    if bundled:
        for node in nodes:
            snippets = [{"kind": "reference", "source": src, "reason": "Available optional context", "symbol": "fixture", "condition": "always"}
                        for src in ({"path": LEMMA["path"], "start": 1, "end": 6}, BACKGROUND)]
            folder = upstream / "source-bundles" / node["id"]
            manifest = materialize(root, folder, node, {"snippets": snippets, "calls": [], "unknowns": [], "coverage": {}})
            node["source_bundle"] = {"path": str(folder.relative_to(upstream)), "manifest_digest": digest(manifest)}
    write_json(upstream / "graph.json", graph)
    status = json.loads((upstream / "status.json").read_text())
    status["graph_digest"] = digest(graph)
    write_json(upstream / "status.json", status)
    requests = []
    result = run_pipeline(root, output, upstream, lambda role, tid: Round2Model(role, tid, requests), budgets=BUDGETS)
    return result, requests


class Round2AcceptanceTests(unittest.TestCase):
    def test_ordinary_and_bundle_real_entry(self):
        for bundled in (False, True):
            with self.subTest(bundled=bundled), tempfile.TemporaryDirectory() as folder:
                base = Path(folder)
                result, requests = run_fixture(base, bundled)
                self.assertEqual(result["status"], "common_candidates_reviewed", result)
                candidate = json.loads((base / "common/candidate.json").read_text())
                self.assertEqual(len(candidate["references"]), 1)
                self.assertEqual(len(candidate["uses"]), 2)
                self.assertNotIn(EXTRA, candidate["uses"][0]["adaptation"])
                self.assertIn(EXTRA, candidate["uses"][1]["adaptation"])
                first = {}
                for request in requests:
                    first.setdefault(request["tid"], request)
                for request in first.values():
                    artifacts, lines = delivered(request["messages"])
                    if request["role"] in ("common", "review"):
                        self.assertNotIn(BACKGROUND["path"], lines)
                        self.assertFalse(any(key.startswith("extract:") for key in artifacts))
                        self.assertNotIn("UNRELATED_BACKGROUND_", json.dumps(request["messages"]))
                    if request["role"] == "common":
                        self.assertIn("needs-summary", artifacts)
                        self.assertFalse(any(key.startswith("spec:") for key in artifacts))
                        rows = artifacts["needs-summary"]["functions"]
                        self.assertEqual([row["needs"][0]["id"] for row in rows], ["identity", "identity"])
                        self.assertNotIn("evidence", rows[0]["needs"][0])
                        self.assertEqual(rows[1]["conditional_assumptions"][0]["condition"], EXTRA)
                        self.assertTrue(all(row["spec_artifact"] and row["extract_artifact"] for row in rows))
                    if request["role"] == "review":
                        self.assertEqual(len([key for key in artifacts if key.startswith("spec:")]), 2)
                        self.assertTrue({1, 2} <= lines["lib/code.c"])
                # Independent role request histories, not inherited extraction reads.
                for role in ("common", "review"):
                    final = [request for request in requests if request["role"] == role][-1]
                    _, lines = delivered(final["messages"])
                    self.assertTrue(set(range(1, 7)) <= lines[LEMMA["path"]])
                # Each final model request contains the delivery history for one
                # independent session. reads.jsonl also contains attempted reads.
                for tid in first:
                    final = [r for r in requests if r["tid"] == tid][-1]
                    seen = set()
                    for message in final["messages"]:
                        if message["role"] != "user":
                            continue
                        try:
                            value = json.loads(message["content"])
                        except ValueError:
                            continue
                        if not isinstance(value, dict) or not value.get("lines"):
                            continue
                        keys = {(value["path"], value["sha256"], line["line"]) for line in value["lines"]}
                        self.assertFalse(seen & keys, (tid, seen & keys))
                        seen.update(keys)

    def test_boundary_source_and_need_summary_are_actual_gates(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            result, _ = run_fixture(base)
            self.assertEqual(result["status"], "common_candidates_reviewed", result)
            output = base / "common"
            candidate = json.loads((output / "candidate.json").read_text())
            review = json.loads((output / "review.json").read_text())
            graph = json.loads((base / "upstream/graph.json").read_text())
            nodes = graph["nodes"]
            reader = Reader(base / "input", base / "isolated-review.jsonl")
            reader.execute({"tool": "read", "path": LEMMA["path"], "start": 1, "count": 3})
            reader.execute({"tool": "read", "path": "lib/code.c", "start": 1, "count": 2})
            artifacts = {"candidate"} | {"spec:" + ident for ident in nodes}
            errors = contracts.review_v3(review, reader, artifacts, proposal=candidate, nodes=nodes)
            self.assertTrue(errors, "Reading the lemma in another role cannot authorize an unread boundary definition")
            reader.execute({"tool": "read", "path": BOUNDARY["path"], "start": 4, "count": 2})
            self.assertEqual(contracts.review_v3(review, reader, artifacts, proposal=candidate, nodes=nodes), [])
            extracts = {ident: json.loads((output / "functions" / ident / "common_needs.json").read_text()) for ident in nodes}
            all_full = artifacts | {"extract:" + ident for ident in nodes}
            errors = contracts.candidate_v3(candidate, reader, all_full, nodes=nodes, extracts=extracts)
            self.assertTrue(any("needs-summary" in error for error in errors), errors)
            self.assertEqual(contracts.candidate_v3(candidate, reader, {"needs-summary"}, nodes=nodes, extracts=extracts), [])

    def test_material_policy_resume_identity(self):
        with tempfile.TemporaryDirectory() as folder:
            base = Path(folder)
            self.assertEqual(run_fixture(base)[0]["status"], "common_candidates_reviewed")
            def no_model(*args):
                self.fail("A completed compatible resume should reuse its validated results")
            self.assertEqual(run_pipeline(base / "input", base / "common", base / "upstream", no_model,
                                          budgets=BUDGETS, resume=True)["status"], "common_candidates_reviewed")
            path = base / "common/identity.json"
            identity = json.loads(path.read_text())
            identity["material_policy"] = 1
            write_json(path, identity)
            with self.assertRaisesRegex(ValueError, "policy|version|changed"):
                run_pipeline(base / "input", base / "common", base / "upstream", no_model,
                             budgets=BUDGETS, resume=True)


if __name__ == "__main__":
    unittest.main()
