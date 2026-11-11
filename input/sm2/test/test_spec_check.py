import tempfile
import unittest
from pathlib import Path

import spec_check


BASE_BODY = "With X Require P(x, X) Ensure P(x, X)"
DERIVED_BODY = "With X Require Q(x, X) Ensure Q(x, X)"


class CallerLocalDerivedTests(unittest.TestCase):
    def make_repo(
        self,
        *,
        caller_base: str = BASE_BODY,
        derived_proof: str = "Proof. exact I. Qed.",
        callee_manual: str = "(* all manual obligations are closed *)",
    ) -> Path:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        source = root / "annotated_C" / "mod"
        vc = root / "rocq" / "vc" / "mod"
        docs = root / "docs"
        source.mkdir(parents=True)
        vc.mkdir(parents=True)
        docs.mkdir(parents=True)

        (source / "callee.c").write_text(
            f"int f(int *x)\n/*@ base {BASE_BODY} */\n"
            "{ return 0; }\n",
            encoding="utf-8",
        )
        (source / "caller.c").write_text(
            f"int f(int *x)\n/*@ base {caller_base} */;\n"
            f"int f(int *x)\n/*@ strong <= base {DERIVED_BODY} */;\n",
            encoding="utf-8",
        )
        (docs / "spec_contract.c").write_text(
            f"int f(int *x)\n/*@ base {BASE_BODY} */;\n",
            encoding="utf-8",
        )

        for case in ("callee", "caller"):
            (vc / f"{case}_proof_auto.v").write_text("", encoding="utf-8")
            (vc / f"{case}_goal_check.v").write_text(
                f"Require Import {case}_goal {case}_proof_auto "
                f"{case}_proof_manual.\n"
                "Module VC_Correctness : VC_Correct.\nEnd VC_Correctness.\n",
                encoding="utf-8",
            )

        (vc / "callee_goal.v").write_text("", encoding="utf-8")
        (vc / "callee_proof_manual.v").write_text(
            callee_manual, encoding="utf-8"
        )
        witness = "f_derive_strong_by_base"
        (vc / "caller_goal.v").write_text(
            f"Definition {witness} := True.\n"
            f"Axiom proof_of_{witness} : {witness}.\n",
            encoding="utf-8",
        )
        (vc / "caller_proof_manual.v").write_text(
            f"Lemma proof_of_{witness} : {witness}.\n{derived_proof}\n",
            encoding="utf-8",
        )
        return root

    def check(self, root: Path) -> list[str]:
        source_files = spec_check.collect_source_files([root / "annotated_C"])
        issues, _, _, _ = spec_check.check_repository(
            root,
            source_files,
            [root / "docs" / "spec_contract.c"],
            require_contract=False,
        )
        return issues

    def test_accepts_proved_derived_from_verified_canonical_base(self):
        self.assertEqual(self.check(self.make_repo()), [])

    def test_rejects_noncanonical_local_base(self):
        issues = self.check(
            self.make_repo(caller_base="With X Require R(x, X) Ensure R(x, X)")
        )
        self.assertTrue(
            any("does not match any canonical callee contract" in issue for issue in issues)
        )

    def test_rejects_unproved_derive_vc(self):
        issues = self.check(self.make_repo(derived_proof="Proof. Admitted."))
        self.assertTrue(
            any("has no Qed/Defined proof" in issue for issue in issues)
        )

    def test_rejects_unproved_callee_base(self):
        issues = self.check(
            self.make_repo(callee_manual="Lemma unfinished : True. Proof. Admitted.")
        )
        self.assertTrue(
            any("callee manual proof still contains Admitted" in issue for issue in issues)
        )

    def test_locates_live_qcp_artifacts_before_scratch_decoys(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        source = (
            root
            / "QCP_examples"
            / "Applications_human"
            / "sm2"
            / "basicOp"
            / "u32_eq.c"
        )
        source.parent.mkdir(parents=True)
        source.write_text("", encoding="utf-8")

        formal = (
            root
            / "Rocq"
            / "examples"
            / "Applications_human"
            / "sm2"
            / "vc"
            / "basicOp"
        )
        formal.mkdir(parents=True)
        formal_goal = formal / "u32_eq_goal.v"
        formal_goal.write_text("", encoding="utf-8")

        decoy = root / ".tmp" / "old" / "vc" / "basicOp"
        decoy.mkdir(parents=True)
        (decoy / "u32_eq_goal.v").write_text("", encoding="utf-8")

        artifacts = spec_check.locate_case_artifacts(root, source)
        self.assertIsNotNone(artifacts)
        self.assertEqual(artifacts.goal, formal_goal)

    def test_skips_explicit_todo_only_central_entry(self):
        root = self.make_repo()
        contract = root / "docs" / "spec_contract.c"
        contract.write_text(
            contract.read_text(encoding="utf-8")
            + "int future(int *x)\n/*@ non_alias TODO */;\n",
            encoding="utf-8",
        )

        source_files = spec_check.collect_source_files([root / "annotated_C"])
        issues, notes, _, _ = spec_check.check_repository(
            root,
            source_files,
            [contract],
            require_contract=False,
        )

        self.assertEqual(issues, [])
        self.assertTrue(
            any("explicit TODO-only" in note and "future" in note for note in notes)
        )

    def test_does_not_skip_unannotated_central_entry(self):
        root = self.make_repo()
        contract = root / "docs" / "spec_contract.c"
        contract.write_text(
            contract.read_text(encoding="utf-8") + "int missing(int *x);\n",
            encoding="utf-8",
        )

        source_files = spec_check.collect_source_files([root / "annotated_C"])
        issues, _, _, _ = spec_check.check_repository(
            root,
            source_files,
            [contract],
            require_contract=False,
        )

        self.assertTrue(
            any("missing: no Require/Ensure contract" in issue for issue in issues)
        )


if __name__ == "__main__":
    unittest.main()
