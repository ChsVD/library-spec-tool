"""Integration tests for stage one, using the pinned graph backend."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from stage1.backend import BASE
from stage1.pipeline import analyze


@unittest.skipUnless(os.environ.get("LST_RUN_GRAPH_TESTS") == "1", "requires pinned graph backend")
class StageOneTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.target, self.reference = self.root / "target", self.root / "ref"
        self.target.mkdir()
        self.reference.mkdir()
        (self.reference / "api.h").write_text("int ref(int);\n")
        (self.reference / "lib.c").write_text(
            'extern int callback(int);\nint ref(int x) { return callback(x); }\n'
            'int same(int x) { return x; }\n'
        )
        (self.target / "feature.h").write_text("static inline int local(int x) { return x; }\n")
        (self.target / "main.c").write_text(
            '#include "api.h"\n#include "feature.h"\n'
            'extern int external(int);\n'
            'int shared(int x) { return local(x); }\n'
            'int rec_b(int);\n'
            'int rec_a(int x) { return x ? rec_b(x - 1) : shared(x); }\n'
            'int rec_b(int x) { return rec_a(x); }\n'
            'int callback(int x) { return shared(x); }\n'
            'static int same(int x) { return shared(x); }\n'
            'int entry(int x) { return ref(x) + rec_a(x) + external(x) + same(x); }\n'
            'int orphan(void) { return shared(0); }\n'
            'int indirect(int (*f)(int), int x) { return f(x); }\n'
            '#if DISABLED\nint inactive(void) { return 0; }\n#endif\n'
        )
        (self.target / "unconfigured.c").write_text("int excluded(void) { return 0; }\n")
        self.database = self.root / "compile_commands.json"
        self.units = [
            {"directory": str(path.parent), "file": str(path),
             "arguments": ["cc", "-I" + str(self.reference), "-DDISABLED=0", "-c", str(path)]}
            for path in [self.target / "main.c", self.reference / "lib.c"]
        ]
        self.database.write_text(json.dumps(self.units))
        self.reuse = self.root / "reuse.json"
        self.reuse.write_text(json.dumps([{"id": "lib", "root": "ref", "materials": ["ref/api.h"]}]))

    def run_stage(self, *entries):
        output = self.root / "run"
        analyze(target=self.target, compile_commands=self.database, output=output,
                         configuration="Linux x86_64 test", entries=entries, reuse_libraries=self.reuse,
                         deps_root=os.environ.get("LST_DEPS_ROOT", BASE))
        return json.loads((output / "stage1.json").read_text())

    def selected(self, result):
        return {result["graph"]["nodes"][i]["name"] for i in result["scope"]["function_ids"]}

    def test_multi_entry_preserves_callback_recursion_and_same_name(self):
        result = self.run_stage("entry", "main.c:orphan")
        self.assertEqual(result["status"], "analysis_completed", result["coverage"])
        self.assertEqual(self.selected(result), {"entry", "orphan", "shared", "local", "rec_a", "rec_b", "same", "callback"})
        nodes = result["graph"]["nodes"]
        self.assertEqual([nodes[e["callee"]]["name"] for e in result["scope"]["reuse_boundaries"]], ["ref"])
        self.assertIn({"rec_a", "rec_b"}, [{nodes[i]["name"] for i in c["functions"]}
                                          for c in result["scope"]["components"]])
        self.assertEqual([c["name"] for c in result["coverage"]["scoped_external_calls"]], ["external"])
        self.assertEqual(result["coverage"]["out_of_configuration_sources"],
                         [{"library": "target", "path": "unconfigured.c"}])
        self.assertFalse((self.target / ".codegraph").exists())
        self.assertEqual([(nodes[e["caller"]]["name"], nodes[e["callee"]]["name"])
                          for e in result["scope"]["callback_dependencies"]], [("entry", "callback")])

    def test_whole_library_reports_unknown_indirect_call(self):
        result = self.run_stage()
        self.assertEqual(result["scope"]["mode"], "whole_library")
        self.assertIn("orphan", self.selected(result))
        self.assertIn("indirect", self.selected(result))
        self.assertNotIn("inactive", self.selected(result))
        self.assertEqual(result["status"], "partial_analysis")
        self.assertTrue(any(g["reason"] == "unresolved_indirect_call" for g in result["coverage"]["scoped_analysis_gaps"]))

    def test_reference_header_without_separate_compilation_unit(self):
        self.database.write_text(json.dumps(self.units[:1]))
        result = self.run_stage("entry")
        nodes = result["graph"]["nodes"]
        boundary, = result["scope"]["reuse_boundaries"]
        self.assertEqual(nodes[boundary["callee"]]["status"], "reference_declaration")
        self.assertEqual(nodes[boundary["callee"]]["name"], "ref")
        self.assertIn("ref", {item["name"] for item in result["graph"]["reuse_index"]})
        self.assertNotIn("callback", self.selected(result))

    def test_analysis_failure_is_partial(self):
        (self.target / "broken.c").write_text(
            '#ifdef __clang__\n#include "missing.h"\n#endif\nint unparsed(void) { return 0; }\n')
        subprocess.run(["gcc", "-c", str(self.target / "broken.c"), "-o", str(self.root / "broken.o")],
                       check=True, capture_output=True)
        self.units.append({"directory": str(self.target), "file": "broken.c",
                           "arguments": ["cc", "-c", "broken.c"]})
        self.database.write_text(json.dumps(self.units))
        result = self.run_stage()
        self.assertEqual(result["status"], "partial_analysis")
        self.assertIn({"library": "target", "path": "broken.c", "status": "analysis_parse_failed"},
                      result["coverage"]["translation_units"])
