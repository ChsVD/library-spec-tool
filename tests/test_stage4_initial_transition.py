import json
import shutil
import unittest
from stage1.runner import snapshot
from stage4.pipeline import run_pipeline
from tests.test_stage4_acceptance import Stage4AcceptanceTests, FixedReferenceModel


class InitialTransitionTests(unittest.TestCase):
    setUp = Stage4AcceptanceTests.setUp

    def prepare(self):
        root = self.base / "expanded"
        shutil.copytree(self.root, root)
        (root / "extra").mkdir()
        (root / "extra/read.v").write_text("(* additional reference *)\n")
        (root / "extra/unrequested.v").write_text("UNREQUESTED_REFERENCE_LINE\n" * 10000)
        added = [{**x, "origin": "fixture"} for x in snapshot(root) if x["path"].startswith("extra/")]
        path = self.base / "transition.json"
        path.write_text(json.dumps({"version": 1, "baseline_root": str(self.root),
            "new_root": str(root), "source_stage3_run": str(self.upstream), "added_files": added}))
        return root, path

    def test_first_run_reads_additions_on_demand_and_resumes(self):
        root, path = self.prepare()
        seen = []
        class Model(FixedReferenceModel):
            def __call__(model, messages, timeout):
                joined = "\n".join(m["content"] for m in messages)
                self.assertNotIn("UNREQUESTED_REFERENCE_LINE", joined)
                if model.role == "common" and '"path": "extra/read.v"' not in joined:
                    return json.dumps({"tool": "read", "path": "extra/read.v", "start": 1, "count": 1,
                                       "draft": "Inspect newly added reference."})
                if '"text": "(* additional reference *)"' in joined:
                    seen.append(model.role)
                return super().__call__(messages, timeout)
        kwargs = dict(budgets=self.budgets, input_transition=path)
        result = run_pipeline(root, self.output, self.upstream, lambda role, tid: Model(role), **kwargs)
        self.assertEqual(result["status"], "common_candidates_reviewed", result)
        self.assertIn("common", seen)
        ident = json.loads((self.output / "identity.json").read_text())
        self.assertEqual(ident["transition_delivery_policy"], "initial-on-demand-v1")
        self.assertTrue((self.output / "input-transition.json").exists())
        self.assertFalse((self.output / "revision-seed.json").exists())
        def no_model(*args):
            self.fail("completed resume must not generate again")
        resumed = run_pipeline(root, self.output, self.upstream, no_model, resume=True, **kwargs)
        self.assertEqual(resumed["status"], result["status"])

    def test_original_changes_or_unlisted_additions_fail_before_model(self):
        root, path = self.prepare()
        def no_model(*args): self.fail("invalid transition must not call model")
        (root / "extra/unlisted.v").write_text("unlisted")
        with self.assertRaisesRegex(ValueError, "allowlist"):
            run_pipeline(root, self.output, self.upstream, no_model, input_transition=path)
        (root / "extra/unlisted.v").unlink()
        (root / "lib/code.c").write_text("changed")
        with self.assertRaisesRegex(ValueError, "modified"):
            run_pipeline(root, self.output, self.upstream, no_model, input_transition=path)

    def test_revision_still_requires_transition(self):
        with self.assertRaisesRegex(ValueError, "requires input-transition"):
            run_pipeline(self.root, self.output, self.upstream, lambda *args: None,
                         revise_from=self.base / "old-run")
