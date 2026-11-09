import json
import os
from pathlib import Path
import tempfile
import unittest

from stage2.fm_graph import adapt
from stage2.inventory import expand_selection
from stage3.reference import run


def manifest(root, paths):
    return expand_selection(root, {"version": 2, "scope_decision": "test scope", "materials": {},
        "selection": {"id": "m", "module_id": "m", "kind": "module", "paths": paths,
                      "configuration": "test configuration", "materials": []}})


class AdapterTests(unittest.TestCase):
    def test_resolved_call_does_not_hide_unknown_call_on_same_line(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d); (root/"a.c").write_text("int leaf(void){return 1;}\nint top(void){return leaf()+missing();}\n")
            m = manifest(root, ["a.c"])
            raw = {"clang_covered": ["leaf", "top"], "indirect_sites": [],
                "functions": [{"fqn": n["symbol"], "symbol": n["symbol"], "file": "a.c",
                               "start": n["source"]["start"], "end": n["source"]["end"],
                               "code": "test", "syntax_error": False,
                               "calls": [{"expression":"leaf","line":2},{"expression":"missing","line":2}] if n["symbol"]=="top" else []}
                              for n in m["functions"]],
                "edges": [{"caller":"top","callee":"leaf","span":{"file":"a.c","start_line":2}}]}
            g = adapt(root, m, raw)
            self.assertEqual([u["symbol"] for u in g["unknown_calls"]], ["missing"])


@unittest.skipUnless(os.environ.get("LST_RUN_GRAPH_TESTS") == "1", "requires provisioned FM-Agent/Clang")
class BackendTests(unittest.TestCase):
    def test_real_backend_and_prepare_only_resume(self):
        with tempfile.TemporaryDirectory() as d:
            base = Path(d); root = base/"input"; root.mkdir()
            (root/"a.c").write_text("""
typedef int (*fn)(int);
static int same(int x){return x+1;}
int ext(int);
#define CALL(x) same(x)
int macro_user(int x){return CALL(x);}
int repeated(int x){return same(x)+same(x+1);}
int dispatch(fn f,int x){return f(x);}
int driver(int x){return dispatch(same,x);}
int unresolved(double (*f)(double),double x){return (int)f(x);}
int outside(int x){return ext(x);}
int rb(int);
int ra(int x){return x ? rb(x-1) : 0;}
int rb(int x){return x ? ra(x-1) : 0;}
#if MODE
int conditional(int x){return ext(x);}
#else
int conditional(int x){return same(x);}
#endif
__attribute__((noinline)) int attributed(int x){return same(x);}
""")
            (root/"b.c").write_text("static int same(int x){return x+2;}\nint other(int x){return same(x);}")
            m = manifest(root, ["a.c", "b.c"])
            g = run(root, base/"out", m, {}, prepare_only=True)
            nodes = g["nodes"]
            pairs = [(nodes[e["caller"]]["symbol"], nodes[e["callee"]]["symbol"]) for e in g["edges"].values()]
            self.assertIn(("macro_user", "same"), pairs)
            self.assertIn(("dispatch", "same"), pairs)
            self.assertIn(("attributed", "same"), pairs)
            for edge in g["edges"].values():
                if nodes[edge["caller"]]["symbol"] == "other":
                    self.assertEqual(nodes[edge["callee"]]["source"]["path"], "b.c")
            repeated = [e for e in g["edges"].values() if nodes[e["caller"]]["symbol"] == "repeated"]
            self.assertEqual(len(repeated[0]["callsites"]), 2)
            self.assertTrue(any({nodes[i]["symbol"] for i in c["members"]} == {"ra","rb"} for c in g["components"]))
            self.assertTrue(any(u.get("symbol") == "ext" or "outside approved" in u["reason"] for u in g["unknown_calls"]))
            self.assertTrue(any("Indirect dispatch" in u["reason"] for u in g["unknown_calls"]))
            self.assertTrue(any("omitted a call site" in u["reason"] for u in g["unknown_calls"]))
            self.assertTrue(any("syntax fallback" in u["reason"] for u in g["unknown_calls"]))
            self.assertFalse((root/".codegraph").exists())
            self.assertEqual(g, run(root, base/"out", m, {}, prepare_only=True, resume=True))

    def test_failed_translation_unit_retains_fallback_and_diagnostics(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)/"input"; root.mkdir()
            (root/"a.c").write_text('#include "not-present.h"\nint leaf(void){return 1;}\nint top(void){return leaf();}')
            g = run(root, Path(d)/"out", manifest(root, ["a.c"]), {}, prepare_only=True)
            self.assertTrue(g["edges"])
            self.assertEqual(g["analysis"]["clang_covered"], [])
            raw = json.loads(Path(g["analysis"]["diagnostics_file"]).read_text())
            self.assertTrue(any(x.get("returncode",0) != 0 for x in raw["diagnostics"]))
            self.assertTrue(g["unknown_calls"])


    def test_supplied_compile_database_controls_active_variant(self):
        with tempfile.TemporaryDirectory() as d:
            base = Path(d); root = base/"input"; root.mkdir()
            (root/"a.c").write_text("#if MODE\nint chosen(void){return 1;}\n#else\nint other(void){return 2;}\n#endif\n")
            database = base/"commands.json"
            database.write_text(json.dumps([{"directory":str(root), "file":str(root/"a.c"),
                "arguments":["cc","-DMODE=1","-c",str(root/"a.c")]}]))
            g = run(root, base/"out", manifest(root, ["a.c"]), {}, prepare_only=True,
                    graph_compile_commands=database)
            active = {n["symbol"] for n in g["nodes"].values() if n.get("fqn") in g["analysis"]["clang_covered"]}
            self.assertEqual(active, {"chosen"})
            self.assertEqual(g["analysis"]["configuration"]["kind"], "supplied-compile-commands")
            raw = json.loads(Path(g["analysis"]["diagnostics_file"]).read_text())
            self.assertTrue(any("-DMODE=1" in d["command"] for d in raw["diagnostics"]))
            database.write_text("[]")
            with self.assertRaisesRegex(ValueError, "resume identity changed"):
                run(root, base/"out", manifest(root, ["a.c"]), {}, prepare_only=True,
                    resume=True, graph_compile_commands=database)
