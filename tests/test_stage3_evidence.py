"""Check production evidence against saved Stage 2 material and source failures."""

import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
import unittest

from stage3.evidence import EvidenceUnavailable, load_evidence
from stage3.index import build_index


ROOT = Path(__file__).resolve().parents[1]
RUN = ROOT / "runs/minimal-simplex-v2-20261118"
STAGE2 = RUN / "stage2-link-evidence-clarified/stage2.json"
STAGE1 = RUN / "stage1/link-evidence-stage1.json"
TRANSFER = ROOT / "runs/stage3-acceptance-20261119/transfer-stage2/stage2.json"


def first_need(evidence, name):
    return next(key for key, need in evidence.needs.items()
                if evidence.nodes[need["function_id"]]["name"] == name)


class ProductionEvidence(unittest.TestCase):
    def test_real_simplex_links_calls_and_named_contracts(self):
        evidence = load_evidence(STAGE2)
        self.assertEqual(len(evidence.needs), 60)
        self.assertEqual(len({need["function_id"] for need in evidence.needs.values()}), 19)
        self.assertEqual({need["status"] for need in evidence.needs.values()}, {"conditional"})
        self.assertEqual(evidence.blocked_functions, [])
        need = first_need(evidence, "build")
        library = evidence.libraries["minigmp"]
        index = build_index([{"id": "minigmp", "root": library["source_root"], "role": "reuse"}])
        payload = evidence.for_need(need, index)
        self.assertEqual(payload["read_errors"], [])
        calls = {row["site"]["location"]["line"]: row for row in payload["calls"]}
        self.assertNotEqual(calls[100]["call_id"], calls[102]["call_id"])
        self.assertEqual(calls[100]["site"]["callee"], calls[102]["site"]["callee"])
        self.assertIn("t.c+r", calls[100]["requirement"]["condition"])
        self.assertIn("q->coef+v+1", calls[102]["requirement"]["condition"])
        for line in (100, 102):
            row = calls[line]
            self.assertEqual([item["check"]["status"] for item in row["checks"]], ["unknown"])
            self.assertIn("neq", row["checks"][0]["check"]["reason"])
        self.assertIn("LP64", payload["configuration"])
        internal = [row for row in payload["calls"] if row["site"]["kind"] == "internal"
                    and row["site"]["caller"] == evidence.needs[need]["function_id"]]
        self.assertEqual(len(internal), 3)
        for row in internal:
            check, = row["checks"]
            self.assertEqual(check["saved_by"], row["site"]["callee"])
        callee = calls[100]["site"]["callee"]
        contract = payload["reuse_contracts"][callee]
        sources = {source["id"]: source for source in payload["sources"]}
        self.assertEqual({(branch["structure"]["branch"], branch["start_line"], branch["end_line"])
                          for branch in contract["branches"]}, {("neq", 39, 44), ("eq", 46, 51)})
        self.assertEqual({row["structure"]["branch"] for row in contract["candidates"]}, {"eq", "neq"})
        for branch in contract["branches"]:
            source = sources[branch["id"]]
            self.assertEqual(source["id"], evidence.read_source(
                source["file_id"], source["start_line"], source["end_line"])["id"])
        self.assertIn("TOPLEVEL_SPEC.md", next(s["path"] for s in sources.values() if s["kind"] == "background"))
        self.assertIn("project/target/src/solver.c", payload["compile_arguments"])

    def test_missing_and_changed_sources_only_block_their_locations(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            relocated = root / STAGE1.name
            shutil.copyfile(STAGE1, relocated)
            shutil.copytree(STAGE1.parent / "project", root / "project")
            evidence = load_evidence(STAGE2, stage1_result=relocated)
            need = first_need(evidence, "build")
            original_sources = evidence.for_need(need)["sources"]
            body = next(row for row in original_sources if row["kind"] == "function_source")
            source = root / body["path"]
            original = source.read_bytes()
            for failure in ("missing", "changed"):
                if failure == "missing":
                    source.unlink()
                else:
                    source.write_bytes(original + b"\n/* changed */\n")
                updated = load_evidence(STAGE2, stage1_result=relocated)
                self.assertEqual(evidence.identity, updated.identity)
                payload = updated.for_need(need)
                body_error = next(row for row in payload["read_errors"] if row["path"] == body["path"]
                                  and row["start_line"] == 83 and row["end_line"] == 107)
                self.assertTrue(body_error["retryable"])
                self.assertFalse(any(row["id"] == body["id"] for row in payload["sources"]))
                self.assertTrue(any(row["kind"] == "background" for row in payload["sources"]))
                with self.assertRaises(EvidenceUnavailable):
                    updated.read_source(body["file_id"], 83, 107)
            source.write_bytes(original)
            self.assertEqual(evidence.for_need(need)["sources"], original_sources)
            relocated.write_bytes(relocated.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "does not match"):
                load_evidence(STAGE2, stage1_result=relocated)

    def test_draft_conflicts_and_missing_drafts_keep_original_requirements(self):
        stage2 = json.loads(STAGE2.read_bytes())
        build = next(row["caller"] for row in stage2["calls"].values()
                     if row["location"] == {"path": "project/target/src/solver.c", "line": 100, "column": 9})
        call_id, site = next((call_id, row) for call_id, row in stage2["calls"].items()
                             if row["caller"] == build and row["kind"] == "internal")
        checked = stage2["functions"][site["callee"]]
        checked["call_checks"][call_id]["status"] = "conflict"
        checked["draft"] = None
        checked["status"] = "blocked"
        checked["reason"] = "upstream contract conflict"
        with TemporaryDirectory() as directory:
            path = Path(directory) / STAGE2.name
            path.write_text(json.dumps(stage2), encoding="utf-8")
            evidence = load_evidence(path)
            need = evidence.needs[first_need(evidence, "build")]
        self.assertIn(call_id, need["conflicting_call_ids"])
        self.assertEqual(need["status"], "conditional")
        blocked, = evidence.blocked_functions
        self.assertEqual(blocked["function_id"], site["callee"])
        self.assertEqual(blocked["status"], "blocked")
        self.assertEqual(blocked["reason"], "upstream contract conflict")

    def test_no_call_and_explicit_supplement(self):
        with TemporaryDirectory() as directory:
            path = Path(directory) / "support.md"
            path.write_text("User supplied evidence.\n", encoding="utf-8")
            evidence = load_evidence(TRANSFER, top_level_spec=path)
            approved = evidence.for_need(first_need(evidence, "gcd32"), build_index([]))
            self.assertEqual(approved["read_errors"], [])
            self.assertEqual(approved["calls"], [])
            self.assertEqual(approved["reuse_contracts"], {})
            supplied, = (row for row in approved["sources"] if row["kind"] == "top_level")
            self.assertEqual(supplied["text"], "User supplied evidence.")
