"""Regression coverage for the production static reference readers."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from stage3.index import build_index


class StaticReferenceIndexTests(unittest.TestCase):
    def setUp(self):
        directory = TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)

    def write(self, path, source):
        path = self.root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        return path

    def test_named_contracts_use_exact_source_identity(self):
        source = (
            '#include "types.h"\n'
            'unsigned long\n'
            'move_value(\n'
            '    holder *dst,\n'
            '    const holder *src\n'
            ')\n'
            '/*@ distinct\n'
            '  With x\n'
            '  Require Packed(dst, 0) * Packed(src, x)\n'
            '  Ensure Packed(dst, x) * Packed(src, x)\n'
            '*/;\n'
            'unsigned long move_value(holder *dst, const holder *src)\n'
            '/*@ alias\n'
            '  With x\n'
            '  Require dst == src && Packed(src, x)\n'
            '  Ensure Packed(dst, x)\n'
            '*/;\n'
            'void caller(void) {\n'
            '  move_value(dst, src)\n'
            '  /*@ spurious\n'
            '    Require False\n'
            '    Ensure True\n'
            '  */;\n'
            '}\n'
        )
        first = self.write("reused/core/edge.c", source)
        self.write("ordinary/core/edge.c", source)
        self.write("reused/core/types.h", '/*@ Import Coq Require Import Specs.Layout */\n')
        self.write("reused/Specs/Layout.v", 'Definition Packed := nat.\n')
        index = build_index([
            {"id": "ordinary", "root": self.root / "ordinary"},
            {"id": "reused", "root": self.root / "reused", "role": "reuse",
             "version": "draft-1", "configuration": {"word_bits": 32}},
        ])
        matches = index.find_contracts("move_value", "reused", "core/edge.c", role="reuse")
        self.assertEqual(matches, index.find_contracts("move_value", "reused", first, role="reuse"))
        self.assertEqual(index.find_contracts("move_value", "reused", "edge.c"), [])
        self.assertEqual([card["structure"]["branch"] for card in matches], ["distinct", "alias"])
        self.assertEqual((matches[0]["start_line"], matches[0]["end_line"]), (2, 11))
        evidence = index.read_entry(matches[0]["id"])
        self.assertTrue(evidence["text"].startswith("unsigned long\nmove_value(\n"))
        self.assertTrue(evidence["contract_text"].startswith("/*@ distinct\n"))
        self.assertEqual(evidence["structure"]["require"], "Packed(dst, 0) * Packed(src, x)")
        self.assertEqual(evidence["configuration"], {"word_bits": 32})
        relations = index.related_entries(evidence["id"])["entries"]
        self.assertTrue(any(row["name"] == "Packed" and row["status"] == "located" for row in relations))

    def test_rocq_boundaries_directions_and_proof_are_read_independently(self):
        source = (
            'Module Storage.\n'
            '(* Outer comment with " (* nested. *) still comment. *)\n'
            'Definition stashed := (let x := 0 in x) : nat.\n'
            'Definition complicated := ([ 0; 1 ]).\n'
            'Lemma forward : forall (map : nat -> nat) a,\n'
            '  Ready a -> Bundle.whole a |-- Bundle.piece (map a) ** Residue a.'
            '(* a period need not have whitespace before this comment *)\n'
            'Proof. { apply other. }\n'
            'Qed.\n'
            'Lemma reverse : forall a, Bundle.piece a ** Residue a |-- Bundle.whole a.\n'
            'Admitted.\n'
            'Definition incomplete := (let y := 0 in y\n'
        )
        self.write("proofs/Storage.v", source)
        index = build_index([{"id": "lib", "root": self.root}])
        file, = index.list_files()["files"]
        hits = index.list_entries(file["id"])["entries"]
        forward, = [r for r in hits if r["name"] == "forward" and r["kind"] == "rocq_declaration"]
        raw = index.read_entry(forward["id"])
        shape = raw["structure"]
        self.assertEqual((raw["start_line"], raw["end_line"]), (5, 6))
        self.assertEqual(shape["parameters"], ["(map : nat -> nat) a"])
        self.assertEqual(shape["premises"], ["Ready a"])
        self.assertEqual(shape["left"], "Bundle.whole a")
        self.assertEqual(shape["right_resources"], ["Bundle.piece (map a)", "Residue a"])
        self.assertEqual(shape["proof_ending"], "Qed")
        self.assertEqual(raw["qualified_name"], "Storage.forward")
        self.assertNotIn("Proof.", raw["text"])
        proof = next(row for row in index.related_entries(forward["id"])["entries"]
                     if row["relation"] == "proof_span")
        self.assertIn("Proof. { apply other. }\nQed.", index.read_entry(proof["id"])["text"])
        self.assertEqual(index.search_references({"kind": "lemma", "have": "bundle whole",
                                                   "need": "piece residue"})["hits"][0]["name"], "forward")
        self.assertEqual(index.search_references({"kind": "lemma", "have": "piece residue",
                                                   "need": "bundle whole"})["hits"][0]["name"], "reverse")
        unknown = next(row for row in hits if row["name"] == "incomplete")
        self.assertEqual(index.read_entry(unknown["id"])["structure"]["status"], "unknown")
        self.assertIn("let y := 0", index.read_entry(unknown["id"])["text"])

    def test_rule_actions_scopes_unknown_and_zero_hits(self):
        self.write("moves.strategies", (
            "// id : 999\n"
            "id : 4\npriority : core(3)\nleft : Wrapped(?p) at 0\n"
            "check : valid(p)\naction : left_erase(0);\n"
            "         left_add(Field(p, n));\n"
            "         custom(move(p));\n"
            "id : 8\nleft : valid(p) at 0\nright : Wrapped(?p) at 1\n"
            "action : right_erase(1);\n  right_add(Field(p, n));\n"
        ))
        self.write("alternate/moves.strategies", "id : 4\naction : left_erase(3);\n")
        manifest = self.write("materials.json", json.dumps({"libraries": [
            {"id": "fixture", "root": ".", "files": ["**/*.strategies"]},
        ]}))
        index = build_index(manifest)
        self.assertEqual(index.identity, build_index(manifest).identity)
        file, = index.list_files(query="moves.strategies", limit=1)["files"]
        hits = index.search_references({"kind": "strategy", "have": "wrapped",
                                       "need": "field", "limit": 1})
        self.assertTrue(hits["truncated"])
        expand, = hits["hits"]
        self.assertEqual(expand["name"], "id 4")
        source = index.read_entry(expand["id"])
        self.assertNotIn("id : 8", source["text"])
        self.assertEqual(source["structure"]["status"], "partial")
        self.assertEqual(source["structure"]["right"], [])
        self.assertIn("valid(p)", source["structure"]["check"][0])
        self.assertEqual(source["structure"]["operations"][-1]["operation"], "unknown")
        self.assertEqual(index.search_references({"kind": "strategy", "need": "wrapped",
            "limit": 1})["hits"][0]["name"], "id 8")
        no_hit = index.search_references("UnobservablXYZqrst")
        self.assertEqual(no_hit["hits"], [])
        self.assertEqual(no_hit["files"], [])
        self.assertEqual(no_hit["scope"]["file_count"], 2)
        self.assertEqual(index.list_entries(file["id"], offset=10)["entries"], [])

    def test_ambiguous_matches_and_read_integrity(self):
        definition = "Definition packed : Prop := True.\n"
        self.write("a/Layout.v", definition)
        alternate = self.write("b/Layout.v", definition)
        self.write("Use.v", "Require Import Layout.\nLemma retrieve : packed.\n")
        self.write("readme.txt", "phrase outside recognized declaration syntax\n")
        index = build_index([{"id": "same", "root": self.root, "files": ["**/*.v", "readme.txt"]}])
        hit, = index.search_references({"symbols": ["retrieve"]})["hits"]
        relations = index.related_entries(hit["id"])
        self.assertEqual(relations["links"][0]["status"], "ambiguous")
        candidates = [row for row in relations["entries"] if row["name"] == "packed"]
        self.assertEqual({row["path"] for row in candidates}, {"a/Layout.v", "b/Layout.v"})
        self.assertEqual({row["status"] for row in candidates}, {"candidate"})
        card, = [row for row in candidates if row["path"] == "b/Layout.v"]
        self.assertEqual(index.read_entry(card["id"])["text"], definition.strip())
        fragment, = index.list_files("phrase")["files"]
        self.assertEqual(fragment["fragment"]["line"], 1)
        alternate.write_text("Definition packed := False.\n", encoding="utf-8")
        with self.assertRaisesRegex(OSError, "changed after indexing"):
            index.read_entry(card["id"])
        alternate.write_text(definition, encoding="utf-8")
        self.assertEqual(index.read_entry(card["id"])["text"], definition.strip())

    def test_outside_link_retains_unreadable_source_location(self):
        outside = self.write("outside.v", "Definition unsafe := True.")
        library = self.root / "inside"
        library.mkdir()
        (library / "over.v").symlink_to(outside)
        index = build_index([{"id": "safe", "root": library}])
        card, = index.list_files()["files"]
        self.assertEqual(card["path"], "over.v")
        self.assertEqual(card["status"], "unreadable")
        self.assertIn("escapes its library root", card["error"])
        self.assertEqual(index.list_entries(card["id"])["entries"], [])


if __name__ == "__main__":
    unittest.main()
