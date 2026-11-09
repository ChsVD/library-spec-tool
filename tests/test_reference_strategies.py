import copy
import json
import tempfile
import unittest
from pathlib import Path
from stage1.reader import Reader
from stage4.strategies import validate, export, verify_export

class StrategyTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.out=self.root/"out";self.out.mkdir()
        (self.root/"rules.strategies").write_text("header\nrule original\nend\n")
        (self.root/"proof.v").write_text("Lemma original.\nQed.\n")
        self.reader=Reader(self.root,self.root/"reads.jsonl")
        self.report={"references":[{"id":"ref"}],"items":[{"id":"item","strategy_ids":["rule"]}],
            "reference_strategies":[{"id":"rule","reference_ids":["ref"],
                "source":{"path":"rules.strategies","start":2,"end":3},
                "proof_sources":[{"path":"proof.v","start":1,"end":2}],
                "dependencies":"original predicate","applicability":"requires adaptation",
                "target_status":"not_validated"}]}
    def read(self):
        self.reader.execute({"tool":"read","path":"rules.strategies","start":2,"count":2})
        self.reader.execute({"tool":"read","path":"proof.v","start":1,"count":2})
    def test_requires_independent_read_and_preserves_text(self):
        self.assertTrue(validate(self.report,self.reader))
        self.read();self.assertEqual(validate(self.report,self.reader),[])
        index=export(self.report,self.reader,self.out)
        self.assertEqual((self.out/"reference_strategies"/index["strategies"][0]["file"]).read_text(),"rule original\nend\n")
        self.assertFalse(index["installed"])
        self.assertEqual(index["strategies"][0]["item_ids"],["item"])
    def test_rejects_dangling_links_and_target_success(self):
        self.read()
        for field,value in [("reference_ids",["missing"]),("target_status","passed"),("id","../escape")]:
            report=copy.deepcopy(self.report);report["reference_strategies"][0][field]=value
            self.assertTrue(validate(report,self.reader))
    def test_missing_proof_must_remain_explicit(self):
        self.read();row=self.report["reference_strategies"][0];row["proof_sources"]=[]
        self.assertTrue(validate(self.report,self.reader))
        row["proof_unknown"]="Not located"
        self.assertEqual(validate(self.report,self.reader),[])
    def test_revision_index_drops_removed_rules(self):
        self.read();export(self.report,self.reader,self.out)
        empty={"references":[],"items":[],"reference_strategies":[]}
        self.assertEqual(validate(empty,self.reader),[])
        index=export(empty,self.reader,self.out)
        self.assertEqual(index["strategies"],[])
        self.assertEqual(json.loads((self.out/"reference_strategies/index.json").read_text())["strategies"],[])

    def test_attachment_tampering_rejected_on_resume(self):
        self.read()
        index=export(self.report,self.reader,self.out)
        verify_export(self.report,self.out)
        (self.out/"reference_strategies"/index["strategies"][0]["file"]).write_text("changed")
        with self.assertRaisesRegex(ValueError,"attachment changed"):
            verify_export(self.report,self.out)
