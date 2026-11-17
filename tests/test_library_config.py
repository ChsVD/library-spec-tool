"""Custom library routing with fixed responses, not semantic model validation."""
import json
from stage1.libraries import load_library_config
from stage1.multi import run_pipeline
from stage1.task import Budgets
import unittest
from tests import test_focused_pipeline as fixtures


class LibraryConfigTests(unittest.TestCase):
    setUp = fixtures.FocusedTests.setUp
    tearDown = fixtures.FocusedTests.tearDown
    cite = fixtures.FocusedTests.cite
    edge = fixtures.FocusedTests.edge
    factory = fixtures.FocusedTests.factory

    def test_config_file_and_capacity(self):
        config = {"target_library": "sm2", "reference_libraries": ["openssl", "mini-gmp"]}
        path = self.base / "libraries.json"
        path.write_text(json.dumps(config))
        self.assertEqual(load_library_config(self.root, path), config)
        with self.assertRaises(ValueError):
            run_pipeline(self.root, self.base / "capacity", lambda *args: self.fail("model called"),
                         library_config=path, max_modules=2)
        self.assertFalse((self.base / "capacity").exists())

    def test_custom_names_end_to_end(self):
        mapping = {"openssl": "solver", "sm2": "arithmetic", "mini-gmp": "collections"}
        for old, new in mapping.items():
            (self.root / old).rename(self.root / new)
        config = {"target_library": "solver", "reference_libraries": ["arithmetic", "collections"]}
        factory, created, _ = self.factory()
        def custom_factory(role, ident):
            original = factory(role, ident)
            def model(messages, timeout):
                prompt = messages[0]["content"]
                self.assertIn('"target_library": "solver"', prompt)
                for old in mapping:
                    self.assertNotIn(old, prompt)
                value = original(messages, timeout)
                for old, new in mapping.items():
                    value = value.replace(old, new)
                return value
            return model
        result = run_pipeline(self.root, self.base / "custom", custom_factory,
            library_config=config, budgets=Budgets(seconds=60, reserve_seconds=0, validation_retries=0))
        self.assertEqual(result["status"], "fixture_pipeline_complete", result)
        self.assertEqual(result["selected_module"], "base")
        self.assertEqual(json.loads((self.base / "custom/library_config.json").read_text()), config)

    def test_invalid_config_rejected_before_model(self):
        for config in [
            {"target_library": "openssl", "reference_libraries": ["openssl"]},
            {"target_library": "../openssl", "reference_libraries": []},
            {"target_library": "missing", "reference_libraries": []},
            {"target_library": "openssl", "reference_libraries": "sm2"},
        ]:
            with self.subTest(config=config), self.assertRaises((ValueError, OSError)):
                run_pipeline(self.root, self.base / "invalid", lambda *args: self.fail("model called"), library_config=config)
            self.assertFalse((self.base / "invalid").exists())

    def test_no_reference_libraries(self):
        self.plan["modules"] = self.plan["modules"][:2]
        self.plan["coverage"] = {"openssl": self.plan["coverage"]["openssl"]}
        self.plan["evidence"] = [self.cite("openssl")]
        factory, created, _ = self.factory(match=False)
        def build(role, ident):
            original = factory(role, ident)
            def model(messages, timeout):
                action = json.loads(original(messages, timeout))
                if role == "screening":
                    if action.get("tool") == "artifact" and action["id"] != "card:base":
                        action = {"tool": "draft", "draft": "No reference configured"}
                    if action.get("tool") == "finish":
                        action["report"]["candidates"] = []
                return json.dumps(action)
            return model
        result = run_pipeline(self.root, self.base / "empty", build,
            library_config={"target_library": "openssl", "reference_libraries": []},
            budgets=Budgets(seconds=60, reserve_seconds=0, validation_retries=0))
        self.assertEqual(result["status"], "fixture_pipeline_complete", result)
        self.assertFalse(any(role == "comparison" for role, _ in created))
