import copy
import hashlib
import tempfile
import unittest
from pathlib import Path

from stage1.reader import Reader
from stage2.source_bundle import extraction_prompt, validate_extraction, materialize, to_original_evidence


class SourceBundleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.root = self.base / 'input'
        self.root.mkdir()
        (self.root / 'a.c').write_bytes(b'int f(int x) {\r\n  return g(x + OFFSET);\r\n}\r\n')
        (self.root / 'a.h').write_text('#define OFFSET 1\ntypedef unsigned word;\nint g(int x);\n', encoding='utf-8')
        self.node = {'id': 'f', 'symbol': 'f', 'source': {'path': 'a.c', 'start': 1, 'end': 3}, 'configuration': 'test'}
        self.selected = {'f': self.node, 'g': {'id': 'g', 'symbol': 'g'}}
        self.report = {'function_id': 'f', 'snippets': [
            {'kind': 'macro', 'source': {'path': 'a.h', 'start': 1, 'end': 1}, 'reason': 'offset', 'symbol': 'OFFSET', 'condition': 'always'},
            {'kind': 'declaration', 'source': {'path': 'a.h', 'start': 3, 'end': 3}, 'reason': 'callee', 'symbol': 'g', 'condition': 'always'}],
            'calls': [{'symbol': 'g', 'target_id': 'g', 'declaration_index': 1, 'callsite': {'path': 'a.c', 'start': 2, 'end': 2}, 'condition': 'always', 'unresolved': ''}],
            'coverage': {'types': 'checked', 'macros': 'checked', 'declarations': 'checked'}, 'unknowns': []}
        self.reader = Reader(self.root, self.base / 'reads.jsonl')
        for name in ('a.c', 'a.h'): self.reader.execute({'tool': 'read', 'path': name})

    def validate(self, report=None, selected=None):
        return validate_extraction(report or self.report, self.reader, {}, node=self.node, selected=selected or self.selected)

    def test_selected_call_cannot_be_externalized(self):
        report=copy.deepcopy(self.report)
        report['calls'][0]['target_id']=None
        self.assertTrue(any('canonical' in e for e in self.validate(report)))
        report['calls'][0]['unresolved']='conditional identity ambiguous'
        report['unknowns']=[{'description':'resolve configuration','blocking':True}]
        self.assertEqual(self.validate(report),[])

    def test_valid_independent_reads(self):
        self.assertEqual(self.validate(), [])
        self.reader.reads.clear()
        self.assertTrue(self.validate())

    def test_exact_lines_and_hashes(self):
        out = self.base / 'example'
        manifest = materialize(self.root, out, self.node, self.report)
        self.assertEqual((out / 'implementation.c').read_text(), 'int f(int x) {\n  return g(x + OFFSET);\n}\n')
        for mapping in manifest['mappings']:
            src = mapping['original']; dst = mapping['bundle']
            original = (self.root / src['path']).read_text().splitlines()[src['start']-1:src['end']]
            copied = (out / dst['path']).read_text().splitlines()[dst['start']-1:dst['end']]
            self.assertEqual(original, copied)
            self.assertEqual(mapping['sha256'], hashlib.sha256((self.root / src['path']).read_bytes()).hexdigest())
            self.assertEqual(to_original_evidence(dst, manifest), src)
        self.assertNotIn('manifest.json', manifest['files'])
        for name, digest in manifest['files'].items(): self.assertEqual(hashlib.sha256((out / name).read_bytes()).hexdigest(), digest)

    def test_gaps_crossings_and_transforms_rejected(self):
        manifest = materialize(self.root, self.base / 'example', self.node, self.report)
        for evidence in ({'path': 'dependencies.h', 'start': 1, 'end': 1}, {'path': 'dependencies.h', 'start': 2, 'end': 5}, {'path': '../a.c', 'start': 1, 'end': 1}):
            with self.assertRaises(ValueError): to_original_evidence(evidence, manifest)
        manifest['mappings'][0]['transformed'] = True
        with self.assertRaises(ValueError): to_original_evidence(manifest['implementation'], manifest)

    def test_bad_declaration_and_outside_callsite(self):
        report = copy.deepcopy(self.report)
        report['snippets'][1]['source'] = self.node['source']
        report['calls'][0]['callsite'] = {'path': 'a.h', 'start': 3, 'end': 3}
        errors = self.validate(report)
        self.assertTrue(any('prototype' in e for e in errors))
        self.assertTrue(any('within target' in e for e in errors))

    def test_duplicate_selected_and_wrong_id(self):
        self.assertTrue(self.validate(selected=[self.node, self.node]))
        report = copy.deepcopy(self.report)
        report['calls'][0]['target_id'] = 'made-up'
        self.assertTrue(any('registry' in e for e in self.validate(report)))
        report['calls'][0]['target_id'] = 'f'
        self.assertTrue(any('symbol' in e for e in self.validate(report)))

    def test_missing_dependency_requires_explicit_gap(self):
        report = copy.deepcopy(self.report)
        report['calls'][0]['declaration_index'] = None
        report['coverage']['declarations'] = 'unknown'
        self.assertTrue(self.validate(report))
        report['calls'][0]['unresolved'] = 'prototype missing'
        report['unknowns'] = [{'description': 'missing declaration', 'blocking': True}]
        self.assertEqual(self.validate(report), [])

    def test_escape_symlink_and_destination_rejected(self):
        outside = self.base / 'secret.h'; outside.write_text('int g(int x);')
        (self.root / 'escape.h').symlink_to(outside)
        for name in ('../secret.h', 'escape.h'):
            report = copy.deepcopy(self.report); report['snippets'][1]['source']['path'] = name
            self.assertTrue(self.validate(report))
            with self.assertRaises(ValueError): materialize(self.root, self.base / 'example', self.node, report)
        with self.assertRaises(ValueError): materialize(self.root, self.root / 'example', self.node, self.report)

    def test_prompt_is_bounded_and_explicit(self):
        prompt = extraction_prompt(self.node, list(self.selected.values()))
        self.assertIn('Do NOT read all callers', prompt)
        self.assertIn('declaration_index', prompt)

    def test_changed_source_invalidates_reads(self):
        with (self.root / 'a.h').open('a') as f: f.write('// changed\n')
        self.assertTrue(self.validate())


if __name__ == '__main__': unittest.main()
