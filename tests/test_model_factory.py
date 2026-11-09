import os
import unittest
from unittest.mock import patch
from stage1.model_factory import ModelConfig, create_model, model_factory
from stage1.codex_backend import BackendError

class FactoryTests(unittest.TestCase):
    def test_each_task_gets_fresh_adapter_with_same_config(self):
        made=[]
        def constructor(*args,**kwargs):
            obj=object();made.append((obj,args,kwargs));return obj
        with patch("stage1.codex_backend.CodexModel",side_effect=constructor):
            factory=model_factory(ModelConfig(model="test",reasoning_effort="high"))
            a=factory("writer","one");b=factory("review","two");c=factory("one-id")
        self.assertIsNot(a,b);self.assertIsNot(b,c)
        self.assertEqual(len(made),3)
        self.assertTrue(all(x[1]==("test",) and x[2]=={"reasoning_effort":"high"} for x in made))

    def test_codex_failure_never_falls_back_to_api(self):
        with patch("stage1.codex_backend.CodexModel",side_effect=BackendError("unavailable")), \
             patch("stage1.runner.APIModel") as api:
            with self.assertRaisesRegex(BackendError,"unavailable"):
                create_model(ModelConfig())
            api.assert_not_called()

    def test_api_explicit_backend_uses_existing_environment(self):
        with patch.dict(os.environ,{"STAGE1_API_URL":"https://example.invalid","STAGE1_MODEL":"m","STAGE1_API_KEY":"secret"}), \
             patch("stage1.runner.APIModel") as api:
            create_model(ModelConfig(backend="api"))
            api.assert_called_once_with("https://example.invalid","m","secret")

    def test_invalid_config_and_secret_repr(self):
        with self.assertRaises(ValueError):ModelConfig(backend="windows")
        with self.assertRaises(ValueError):ModelConfig(backend="api",reasoning_effort="high")
        with self.assertRaises(ValueError):ModelConfig(api_key="secret")
        self.assertNotIn("secret",repr(ModelConfig(backend="api",api_key="secret")))
        with patch.dict(os.environ,{},clear=True):
            with self.assertRaises(BackendError):create_model(ModelConfig(backend="api"))
