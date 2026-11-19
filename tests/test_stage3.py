import json
from pathlib import Path
import re
from tempfile import TemporaryDirectory
import unittest

from stage3.__main__ import run
from stage3.offline import commit_review
from stage3.references import ReferenceIndex


ROOT = Path(__file__).resolve().parents[1]
STAGE2 = ROOT / "runs/minimal-simplex-v2-20261118/stage2-link-evidence-clarified/stage2.json"
REFERENCE = ROOT / "example/minimal-simplex/references/fme/Rocq/fme_gmp_lib.v"
FIXTURE = ROOT / "tests/fixtures/stage3-simplex-review.json"


class OfflineAcceptance(unittest.TestCase):
    def setUp(self):
        self.fixture = json.loads(FIXTURE.read_bytes())

    def test_frozen_stage2_and_full_reference(self):
        result = run(STAGE2, REFERENCE, self.fixture)
        original = json.loads(STAGE2.read_bytes())
        need = result["need"]
        self.assertEqual(result["stage2"]["statuses"], {"conditional": 19})
        self.assertEqual(result["stage2"]["common_needs"], 60)
        self.assertEqual(need["status"], "conditional")
        fn = original["functions"][need["function_id"]]
        self.assertEqual(need["original"], fn["draft"]["common_needs"][0])
        site = next(c for c in need["calls"] if c["site"]["location"]["line"] == 102)
        self.assertEqual(site["checks"][0]["check"]["status"], "unknown")
        self.assertIn("Arch32", site["checks"][0]["check"]["reason"])
        callee_checks = [c for c in need["calls"] if c["site"]["kind"] == "internal"]
        self.assertEqual(len(callee_checks), 3)
        for call in callee_checks:
            check, = call["checks"]
            self.assertEqual(check["saved_by"], call["site"]["callee"])
            self.assertEqual(check["check"]["status"], "compatible")

        self.assertEqual(result["index"]["declarations"], 50)
        split = result["searches"]["split"]
        merge = result["searches"]["merge"]
        self.assertEqual(len(split["top_five"]), 5)
        self.assertEqual(len(merge["top_five"]), 5)
        self.assertEqual([c["start"] for c in split["ranking"][:2]], [80, 236])
        self.assertEqual([c["start"] for c in merge["ranking"][:2]], [70, 281])
        self.assertGreater(split["ranking"][1]["score"], split["ranking"][6]["score"])
        self.assertGreater(merge["ranking"][1]["score"], merge["ranking"][3]["score"])
        self.assertEqual(result["coverage"], "partial")
        self.assertEqual(len(result["uses"]), 2)
        lines = REFERENCE.read_text().splitlines()
        for use in result["uses"]:
            self.assertEqual(use["target_validation"], "not_run")
            self.assertEqual(use["need_id"], need["id"])
            self.assertEqual(use["call_id"], site["call_id"])
            item = result["items"][use["entry_id"]]
            self.assertEqual(item["source"], "\n".join(lines[item["start"] - 1:item["end"]]).strip())
        self.assertTrue(all(any(token in gap for gap in result["remaining"])
                            for token in ("表示", "同值替换", "dummy", "LP64")))
        with self.assertRaisesRegex(ValueError, "was not delivered"):
            commit_review(need, result["delivered"][:1], result["review"])

    def test_roles_survive_renaming_and_unknown_notation_is_preserved(self):
        text = REFERENCE.read_text()
        replacements = {
            "mpz_coef_array": "row_resource",
            "mpz_coef_array_missing_i_rec": "borrowed_row_resource",
            "mpz_coef_array_split": "lemma_a",
            "mpz_coef_array_merge": "lemma_b",
            "mpz_store": "slot_resource",
        }
        text = re.sub(r"\w+", lambda m: replacements.get(m[0], m[0]), text)
        text += "\n(* Nested (* Lemma decoy: True. *) comment. *)\nLemma opaque: X @@ Y.\n"
        with TemporaryDirectory() as directory:
            source = Path(directory) / "renamed.v"
            source.write_text(text)
            index = ReferenceIndex(source)
        for trial, expected in zip(self.fixture["trials"], ("lemma_a", "lemma_b"), strict=True):
            self.assertEqual(index.search(**trial["query"])[1]["name"], expected)
        opaque, = (entry for entry in index.entries.values() if entry["name"] == "opaque")
        self.assertIsNone(opaque["structure"])
        self.assertEqual(opaque["source"], "Lemma opaque: X @@ Y.")
        self.assertFalse(any(entry["name"] == "decoy" for entry in index.entries.values()))

