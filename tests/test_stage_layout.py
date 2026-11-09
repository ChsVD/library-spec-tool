"""Regression checks for the four-stage entrypoints."""
import importlib
import unittest
from unittest.mock import patch


class StageLayoutTests(unittest.TestCase):
    def test_graph_entry_is_always_static_and_rejects_model_callback(self):
        from stage2.__main__ import main
        def prepare(*args, **kwargs):
            self.assertTrue(kwargs['prepare_only'])
            with self.assertRaisesRegex(RuntimeError, 'must not invoke'):
                args[4]('unexpected-model')
            return {'nodes': {}, 'components': []}
        with patch('stage2.__main__.load_manifest', return_value=({}, {})), \
             patch('stage3.reference.run', side_effect=prepare), \
             patch('stage1.codex_backend.CodexModel') as backend, patch('builtins.print'):
            self.assertEqual(main(['--manifest', 'manifest.json', '--output', 'out']), 0)
            backend.assert_not_called()

    def test_graph_entry_rejects_generation_options(self):
        from stage2.__main__ import main
        with patch('sys.stderr'), self.assertRaises(SystemExit) as caught:
            main(['--manifest', 'manifest.json', '--output', 'out', '--with-common'])
        self.assertEqual(caught.exception.code, 2)

    def test_spec_entry_uses_natural_spec_implementation(self):
        from stage3.__main__ import main
        from stage3.reference import main as reference_main
        self.assertIs(main, reference_main)

    def test_common_entry_accepts_new_and_legacy_upstream_flags(self):
        from stage4.__main__ import main
        for flag in ['--stage3-run', '--stage2-run']:
            with self.subTest(flag=flag), \
                 patch('sys.argv', ['stage4', flag, 'spec-run', '--output', 'common-run']), \
                 patch('stage1.codex_backend.CodexModel'), \
                 patch('stage4.__main__.run_pipeline', return_value={'status': 'common_candidates_reviewed'}) as run, \
                 patch('builtins.print'):
                self.assertEqual(main(), 0)
                self.assertEqual(run.call_args.args[2], 'spec-run')

    def test_legacy_module_imports_share_the_implementation(self):
        for name in ['reference', 'reference_review', 'read_materials', 'scenario_guidance']:
            self.assertIs(importlib.import_module('stage2.' + name),
                          importlib.import_module('stage3.' + name))
