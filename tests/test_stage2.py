"""Stage-two pipeline tests with fixed writer and reviewer responses."""
import json
import os
from pathlib import Path
import tempfile
import unittest

from stage1.graph import compute_scope
from stage1.inputs import sha256
from stage1.pipeline import analyze
from stage2.pipeline import run


class StageTwoTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        project = self.root / "stage1/project"
        self.project = project
        self.nodes = {}
        self.edges = {}
        self.gaps = []
        self.output = self.root / "stage2"
        self.writes = []
        self.audits = []
        self.interrupt = None
        self.conflict = set()

    def source(self, name, text, library="target", definition=True):
        path = self.project / library / (name + ".c")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text + "\n")
        self.nodes[name] = {
            "id": name, "name": name, "symbol": name, "library": library, "type": "int (void)",
            "source": {"path": path.name, "line": 1, "column": 1, "end_line": len(text.splitlines())},
            "status": "definition" if definition else "reference_declaration",
        }

    def edge(self, caller, callee):
        self.edges[f"{caller}-{callee}"] = {
            "caller": caller, "callee": callee,
            "callsites": [{"path": self.nodes[caller]["source"]["path"], "line": 1, "column": 1,
                           "kind": "direct", "evidence": "fixture"}],
        }

    def prepare(self, entries=()):
        graph = {"nodes": self.nodes, "edges": self.edges, "analysis_gaps": self.gaps, "external_calls": []}
        scope = compute_scope(graph, entries)
        self.input = self.root / "stage1/stage1.json"
        libraries = {node["library"] for node in self.nodes.values()}
        self.input.write_text(json.dumps({
            "schema_version": 1, "status": "partial_analysis" if self.gaps else "analysis_completed",
            "configuration": "Linux x86_64",
            "libraries": {name: {"snapshot_root": "project/" + name} for name in libraries},
            "graph": graph, "scope": scope, "coverage": {"translation_units": []},
            "provenance": {"snapshot_files": [
                {"path": file.relative_to(self.project).as_posix(), "sha256": sha256(file)}
                for file in self.project.rglob("*") if file.is_file()
            ]},
        }))

    def factory(self, role, ident):
        def model(messages, timeout):
            data = json.loads(messages[1]["content"])
            task = data["task"]
            if role == "write":
                if self.interrupt in task["members"]:
                    raise KeyboardInterrupt()
                first = len(messages) == 2
                if first:
                    self.writes.append(tuple(task["members"]))
                proposals = []
                first_callback_pass = "dispatch" in task["members"] and all(
                    call["callee"] != "target_callback" for call in task["outgoing"].values())
                if first_callback_pass:
                    ref = {"path": "project/target/table.h", "start": 1, "end": 1}
                    if first:
                        return json.dumps({"tool": "read", "path": ref["path"], "start": 1, "count": 1})
                    proposals.append({"caller": "dispatch", "callee": "target_callback",
                                      "path": "project/target/dispatch.c", "line": 1, "column": 1,
                                      "condition": "fixed table", "reason": "pointer initializer",
                                      "evidence": [{"path": "project/target/dispatch.c", "start": 1, "end": 1}, ref]})
                report = {"functions": [], "edge_proposals": proposals}
                for function, source in data["source"].items():
                    evidence = [{key: source[key] for key in ("path", "start", "end")}]
                    report["functions"].append({
                        "function_id": function, "purpose": "fixture", "symbols": "fixture",
                        "cases": [{"name": "default", "with": "none", "require": "true", "ensure": "fixture"}],
                        "assumptions": [], "uncovered": [], "evidence": evidence,
                        "call_requirements": [
                            {"call_id": k, "condition": f"scenario for {function}",
                             "available": "fixture resources", "needed": "fixture guarantee"}
                            for k, call in task["outgoing"].items() if call["caller"] == function
                        ],
                        "common_needs": [{
                            "kind": "definition", "use": "default postcondition",
                            "need": "fixture representation", "evidence": evidence,
                        }] if function == "entry" else [],
                    })
            else:
                self.audits.append((tuple(task["members"]), data["audit_calls"]))
                report = {
                    "functions": [{"function_id": ident, "status": "approved", "reason": "fixture"}
                                  for ident in task["members"]],
                    "call_checks": [
                        {"call_id": k, "status": ("unknown" if row["incomplete"] else
                                                  "conflict" if row["call"]["callee"] in self.conflict
                                                  else "compatible"), "reason": "fixture review"}
                        for k, row in data["audit_calls"].items()
                    ],
                    "edge_reviews": [{"proposal_id": k, "accept": True, "reason": "verified fixture initializer"}
                                     for k in data["edge_proposals"]],
                }
            return json.dumps({"tool": "finish", "report": report})
        return model

    def run_stage(self, **kwargs):
        return run(stage1_result=self.input, output=self.output, model_factory=self.factory,
                   max_revisions=0, **kwargs)

    def test_multi_caller_and_recursive_contracts(self):
        for ident in ("entry", "other", "leaf", "a", "b"):
            self.source(ident, f"int {ident}(void) {{ return 0; }}")
        for caller, callee in [("entry", "leaf"), ("other", "leaf"), ("leaf", "a"), ("a", "b"), ("b", "a")]:
            self.edge(caller, callee)
        self.prepare()
        result = self.run_stage()
        self.assertEqual(result["status"], "completed")
        leaf = next(data for group, data in self.audits if group == ("leaf",))
        self.assertEqual({row["requirement"]["condition"] for row in leaf.values()},
                         {"scenario for entry", "scenario for other"})
        self.assertIn(("a", "b"), self.writes)
        self.assertTrue(result["functions"]["entry"]["draft"]["common_needs"])

    def test_recursive_member_batches_resume_at_exact_count_and_review_both_endpoints(self):
        for ident in ("entry", "a", "b", "c", "d", "e", "tail"):
            self.source(ident, f"int {ident}(void) {{ return 0; }}")
        for caller, callee in [("entry", "a"), ("a", "b"), ("b", "c"), ("c", "d"),
                               ("d", "e"), ("e", "a"), ("e", "tail")]:
            self.edge(caller, callee)
        self.prepare(["entry"])
        first = self.run_stage(stop_after_functions=4, member_batch_size=2)
        self.assertEqual(self.writes, [("entry",), ("a", "b"), ("c",)])
        self.assertEqual(set(first["functions"]), {"entry", "a", "b", "c"})
        self.assertEqual(first["status"], "in_progress")
        self.assertTrue(any(set(row["functions"]) == {"a", "b", "c", "d", "e"}
                            for row in first["scope"]["components"]))
        calls = {(row["caller"], row["callee"]): key for key, row in first["calls"].items()}
        forward = calls["c", "d"]
        backward = calls["e", "a"]
        self.assertEqual(first["functions"]["c"]["call_checks"][forward]["status"], "unknown")
        self.assertEqual(first["functions"]["a"]["call_checks"][backward]["status"], "unknown")
        self.assertEqual(first["functions"]["b"]["call_checks"][calls["b", "c"]]["status"], "compatible")

        self.writes.clear()
        later = self.run_stage(resume=True, stop_after_functions=6)
        self.assertEqual(self.writes, [("d", "e")])
        self.assertEqual(len(later["functions"]), 6)
        self.assertEqual(later["functions"]["entry"], first["functions"]["entry"])
        self.assertEqual(later["functions"]["a"]["status"], "approved")
        for ident, check in [("c", forward), ("d", forward), ("e", backward), ("a", backward)]:
            self.assertEqual(later["functions"][ident]["call_checks"][check]["status"], "compatible")

        self.writes.clear()
        result = self.run_stage(resume=True)
        self.assertEqual(self.writes, [("tail",)])
        self.assertEqual(result["status"], "completed")

    def test_revisions_only_rewrite_rejected_functions_and_recheck_adjacent_calls(self):
        for name, target in (("a", "b"), ("b", "c"), ("c", "a")):
            self.source(name, f"int {name}(void) {{ return {target}(); }}")
            self.edge(name, target)
        self.prepare(["a"])
        writes, audits, originals = [], [], {}

        def factory(role, ident):
            original = self.factory(role, ident)

            def model(messages, timeout):
                data = json.loads(messages[1]["content"])
                task = data["task"]
                report = json.loads(original(messages, timeout))["report"]
                if role == "write":
                    writes.append(set(task["members"]))
                    for draft in report["functions"]:
                        key = draft["function_id"]
                        if len(writes) == 1:
                            originals[key] = dict(draft)
                        else:
                            self.assertEqual(data["previous_drafts"], {key: originals[key]})
                            self.assertIn(key, data["previous_review"]["functions"])
                            self.assertIn("a", task["peer_contracts"])
                            draft["purpose"] = "revised " + key
                else:
                    pairs = {k: (v["call"]["caller"], v["call"]["callee"])
                             for k, v in data["audit_calls"].items()}
                    audits.append(set(pairs.values()))
                    for row in report["functions"]:
                        if len(audits) == 1 and row["function_id"] == "b":
                            row.update(status="blocked", reason="missing a case")
                    conflict = {1: ("a", "b"), 2: ("b", "c")}.get(len(audits))
                    for row in report["call_checks"]:
                        if pairs[row["call_id"]] == conflict:
                            row.update(status="conflict", reason="precondition mismatch")
                return json.dumps({"tool": "finish", "report": report})
            return model

        result = run(stage1_result=self.input, output=self.output, model_factory=factory, max_revisions=1)
        self.assertEqual(writes, [{"a", "b", "c"}, {"b"}, {"c"}])
        self.assertEqual(audits[1:], [{("a", "b"), ("b", "c")}, {("b", "c"), ("c", "a")}])
        self.assertEqual(result["functions"]["a"]["draft"], originals["a"])
        self.assertEqual(result["status"], "completed")

    def test_reuse_conflict_keeps_independent_result(self):
        self.source("entry", "int entry(void) { return ref(); }")
        self.source("independent", "int independent(void) { return 0; }")
        self.source("ref", "int ref(void);", "proven", False)
        self.edge("entry", "ref")
        self.prepare()
        contract = self.root / "contract.txt"
        contract.write_text("existing contract\n")
        declaration = self.root / "contracts.json"
        declaration.write_text(json.dumps({"ref": {"path": "contract.txt", "start": 1, "end": 1}}))
        self.conflict.add("ref")
        result = self.run_stage(reuse_contracts=declaration)
        self.assertEqual(result["status"], "partial")
        self.assertEqual(result["functions"]["entry"]["status"], "blocked")
        self.assertEqual(result["functions"]["independent"]["status"], "approved")

    def test_reviewed_named_call_uses_id_from_read_and_reschedules(self):
        self.check_reviewed_named_call(ambiguous=True)

    def test_unique_reviewed_named_target_replaces_gap(self):
        self.check_reviewed_named_call(ambiguous=False)

    def check_reviewed_named_call(self, ambiguous):
        self.source("entry", "int entry(void) { return helper(); }")
        for key in ("fn-local", "fn-other"):
            name = "helper" if ambiguous or key == "fn-local" else "other"
            self.source(key, f"int {name}(void) {{ return 0; }}")
            self.nodes[key].update(name=name, symbol=name)
        self.gaps.append({"caller": "entry", "location": {"path": "entry.c", "line": 1, "column": 26},
                          "name": "helper", "reason": "unconfirmed_call_target", "candidate_ids": []})
        self.prepare(["entry"])

        def factory(role, ident):
            original = self.factory(role, ident)

            def model(messages, timeout):
                data = json.loads(messages[1]["content"])
                outgoing = data["task"]["outgoing"].values()
                propose = role == "write" and ident == "entry" and not any(c["callee"] for c in outgoing)
                if propose and len(messages) == 2:
                    return json.dumps({"tool": "read", "path": "project/target/fn-local.c", "start": 1, "count": 1})
                response = json.loads(original(messages, timeout))
                report = response["report"]
                if propose:
                    read = json.loads(messages[-1]["content"])
                    definition, = read["definitions"]
                    self.assertEqual(definition["name"], "helper")
                    report["edge_proposals"].append({
                        "caller": ident, "callee": definition["function_id"],
                        "path": "project/target/entry.c", "line": 1, "column": 26,
                        "condition": "when reached", "reason": "fixture direct call",
                        "evidence": [{"path": path, "start": 1, "end": 1}
                                     for path in ("project/target/entry.c", read["path"])]})
                if role == "review":
                    for row in report["call_checks"]:
                        row["status"] = "compatible"
                return json.dumps(response)
            return model

        result = run(stage1_result=self.input, output=self.output, model_factory=factory)
        self.assertEqual(set(result["functions"]), {"entry", "fn-local"})
        self.assertEqual(len(result["accepted_edges"]), 1)
        if not ambiguous:
            self.assertEqual(result["status"], "completed")
            self.assertEqual(result["analysis_gaps"], [])
            call, = result["calls"].values()
            self.assertEqual(call["detail"]["source_kind"], "direct")
            self.assertEqual(call["detail"]["resolved_stage1_gap"], self.gaps[0])
            self.assertEqual(json.loads(self.input.read_text())["graph"]["analysis_gaps"], self.gaps)
            return
        self.assertEqual(result["functions"]["entry"]["status"], "conditional")
        unresolved, = result["functions"]["entry"]["call_checks"].values()
        self.assertEqual((unresolved["status"], unresolved["reviewed_status"]), ("unknown", "compatible"))

    def test_resume_rebuilds_supplemented_scope(self):
        self.source("entry", "int entry(void) { return dispatch(); }")
        self.source("dispatch", "int dispatch(void) { return ops->run(); }")
        self.source("target_callback", "int target_callback(void) { return tail(); }")
        self.source("tail", "int tail(void) { return 0; }")
        (self.project / "target/table.h").write_text("fixed_ops = {.run=target_callback};\n")
        self.edge("entry", "dispatch")
        self.edge("target_callback", "tail")
        self.gaps.append({"caller": "dispatch", "location": {"path": "dispatch.c", "line": 1, "column": 1},
                          "reason": "unresolved_indirect_call"})
        self.prepare(["entry"])
        self.interrupt = "target_callback"
        with self.assertRaises(KeyboardInterrupt):
            self.run_stage()
        saved = json.loads((self.output / "stage2.json").read_text())
        self.assertIn("entry", saved["functions"])
        self.assertEqual(len(saved["accepted_edges"]), 1)
        self.assertEqual(set(saved["scope"]["function_ids"]), {"entry", "dispatch", "target_callback", "tail"})
        completed = set(saved["functions"])
        self.interrupt = None
        self.writes.clear()
        result = self.run_stage(resume=True)
        self.assertEqual(result["status"], "partial")
        self.assertEqual(set(result["functions"]), {"entry", "dispatch", "target_callback", "tail"})
        self.assertTrue(result["analysis_gaps"])
        self.assertFalse(completed & {ident for group in self.writes for ident in group})
        old_input = json.loads(self.input.read_text())
        self.assertEqual(set(old_input["scope"]["function_ids"]), {"entry", "dispatch"})

    @unittest.skipUnless(os.environ.get("LST_RUN_GRAPH_TESTS") == "1", "requires pinned graph backend")
    def test_real_stage1_handoff_for_entries(self):
        target = self.root / "actual"
        target.mkdir()
        source = target / "actual.c"
        source.write_text("int leaf(int x) { return x; }\n"
                          "int entry(int x) { return leaf(x); }\n"
                          "int out_of_scope(void) { return leaf(1); }\n")
        database = self.root / "compile_commands.json"
        database.write_text(json.dumps([{"directory": str(target), "file": str(source),
                                        "arguments": ["cc", "-c", str(source)]}]))
        upstream = self.root / "actual-run"
        deps = os.environ.get("LST_DEPS_ROOT", Path(__file__).resolve().parents[1])
        stage1 = analyze(target=target, compile_commands=database, output=upstream,
                         configuration="Linux x86_64", entries=["entry"], deps_root=deps)
        self.input = upstream / "stage1.json"
        result = self.run_stage()
        self.assertEqual(result["status"], "completed")
        self.assertEqual({stage1["graph"]["nodes"][ident]["name"] for ident in result["functions"]},
                         {"entry", "leaf"})
        self.assertEqual(len(result["calls"]), 1)

    def test_resume_refuses_changed_source(self):
        self.source("entry", "int entry(void) { return 0; }")
        self.prepare()
        self.run_stage()
        self.writes.clear()
        self.assertEqual(self.run_stage(resume=True)["status"], "completed")
        self.assertEqual(self.writes, [])
        (self.project / "target/entry.c").write_text("int entry(void) { return 1; }\n")
        with self.assertRaisesRegex(ValueError, "snapshot file changed"):
            self.run_stage(resume=True)


if __name__ == "__main__":
    unittest.main()
