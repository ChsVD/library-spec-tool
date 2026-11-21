"""Production stage-two tool exchange, using deterministic independent model responses."""
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest

from stage1.graph import compute_scope
from stage1.inputs import sha256
from stage1.pipeline import analyze
from stage2.contract_store import ContractStore
from stage2.contract_tools import ContractLog
from stage2.pipeline import run


SPEC = {
    "id": "stdlib/stdarg/va_list_lifecycle",
    "source": "WG14 N1570 §7.16.1, §7.16.1.3–4",
    "operations": {
        "__builtin_va_start": {"name": "va_start", "requires": "Valid last named parameter and list.",
                                "ensures": "Initializes the designated argument list."},
        "__builtin_va_end": {"name": "va_end", "requires": "A matching active list.",
                              "ensures": "Ends this use of the argument list."}},
    "checks": ["Check initialization and matching end in the same function on each return path."]}


class ContractToolTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.store = self.root / "contracts"
        self.unit = self.root / "input/project/lib-target/trial.c"
        self.unit.parent.mkdir(parents=True)
        self.unit.write_text("#include <stdarg.h>\nint trial(int last, ...) {\n va_list ap;\n"
                             " va_start(ap,last);\n va_end(ap);\n return last;\n}\n")
        command = {"file": str(self.unit), "directory": str(self.unit.parent),
                   "arguments": ["clang", "-std=c11", "-c", str(self.unit)]}
        db = self.unit.parents[1] / "compile_commands.json"
        db.write_text(json.dumps([command]))
        node = {"library": "target", "id": "trial", "name": "trial", "symbol": "trial",
                "status": "definition", "source": {"path": "trial.c", "line": 2, "column": 5, "end_line": 7},
                "translation_units": [{"library": "target", "path": "trial.c"}], "type": "int (int, ...)"}
        graph = {"nodes": {"trial": node}, "edges": {}, "analysis_gaps": [], "external_calls": [
            {"caller": "trial", "kind": "compiler_builtin", "name": name,
             "location": {"path": "trial.c", "line": i, "column": 2}} for i, name in enumerate(SPEC["operations"], 4)]}
        self.stage1 = self.unit.parents[2] / "stage1.json"
        self.stage1.write_text(json.dumps({
            "schema_version": 1, "configuration": "test", "status": "analysis_completed",
            "libraries": {"target": {"snapshot_root": "project/lib-target"}}, "scope": compute_scope(graph, ["trial"]),
            "graph": graph, "coverage": {"translation_units": []},
            "provenance": {"clang_version": "clang fixture", "clang_default_target": "x86_64-linux",
                           "snapshot_files": [{"path": f.relative_to(db.parent).as_posix(),
                                               "sha256": sha256(f)} for f in (self.unit, db)]}}))
        self.decisions = []
        self.reject_first = True
        self.modify = False
        self.abstain = False
        self.requests = []

    def factory(self, role, ident):
        def model(messages, timeout):
            data = json.loads(messages[1]["content"])
            self.requests.append(data)
            finish = lambda report: json.dumps({"tool": "finish", "report": report})
            if "proposals" in data:
                if len(messages) == 2:
                    proposal = data["proposals"][0]
                    decision = "reject" if self.reject_first and not self.decisions else "approve"
                    self.decisions.append(decision)
                    return json.dumps({"tool": "review_contract_change", "proposal_id": proposal["proposal_id"],
                                       "decision": decision, "reason": "fixture independent finding"})
                return finish({})
            task = data["task"]
            if role == "write":
                calls = list(data["builtin_calls"])
                if len(messages) == 2:
                    return json.dumps({"tool": "lookup_contract", "call_ids": calls})
                if len(messages) == 4:
                    response = json.loads(messages[-1]["content"])
                    hit = response["calls"][calls[0]]
                    self.assertLessEqual(len(response["rules"]), 1)
                    if not self.abstain and (hit["status"] == "missing" or (self.modify and hit.get("version") == 1)):
                        spec = deepcopy(SPEC)
                        if self.decisions:
                            spec["checks"].append("Check identity of the list.")
                        if self.modify:
                            spec["checks"].append("Check reinitialization.")
                        return json.dumps({"tool": "propose_contract_change", "call_ids": calls,
                                           "reason": "fixture amendment", "base_version": hit.get("version", 0),
                                           "spec": spec})
                source, = data["source"].values()
                return finish({"functions": [{"function_id": ident, "purpose": "test", "symbols": "ap",
                    "cases": [{"name": "default", "with": "ap", "require": "valid", "ensure": "returns"}],
                    "assumptions": [], "uncovered": [], "evidence": [
                        {k: source[k] for k in ("path", "start", "end")}], "common_needs": [],
                    "call_requirements": [{"call_id": k, "condition": "on path", "available": "list",
                                           "needed": "valid phase"} for k in task["outgoing"]]}],
                    "edge_proposals": []})
            early_return = "if(last<0) return 0;" in data["source"][ident]["text"]
            return finish({"functions": [{"function_id": ident, "status": "approved", "reason": "fixture"}],
                           "edge_reviews": [], "call_checks": [{"call_id": k, "reason": "fixture path audit",
                           "status": "conflict" if early_return and row["call"]["detail"]["name"] == "__builtin_va_end" else "compatible"} for k, row in data["audit_calls"].items()]})
        return model

    def stage(self, name, **kwargs):
        return run(stage1_result=self.stage1, output=self.root / name, model_factory=self.factory,
                   contract_store_root=self.store, max_revisions=0, **kwargs)

    def test_reject_create_reuse_modify_and_resume(self):
        result = self.stage("first")
        self.assertEqual(self.decisions, ["reject", "approve"])
        self.assertEqual(result["status"], "completed")
        self.assertTrue(any(d.get("contract_change_feedback", [{}])[0].get("status") == "rejected"
                            for d in self.requests))
        changes = json.loads((self.root / "first/contract-changes.json").read_text())
        self.assertEqual([p["status"] for p in changes["events"]], ["rejected", "approved"])
        record, = result["functions"].values()
        self.assertEqual({c["contract"]["version"] for c in record["call_checks"].values()}, {1})
        self.stage("reuse")
        self.assertEqual(json.loads((self.root / "reuse/contract-changes.json").read_text())["events"], [])
        self.modify = True
        self.stage("modified")
        log = json.loads((self.root / "modified/contract-changes.json").read_text())
        row, = log["events"]
        self.assertEqual((row["operation"], row["base_version"], row["proposed_version"]), ("modify", 1, 2))
        self.assertNotEqual(row["before"], row["spec"])
        self.assertEqual(result, self.stage("first", resume=True))

    def test_cas_recovery_and_scope_mismatch(self):
        self.reject_first = False
        self.stage("first")
        log = ContractLog(self.root / "first", ContractStore(self.store))
        row = log.data["events"][0]
        row["status"] = "publishing"
        log.save()
        recovered = ContractLog(self.root / "first", ContractStore(self.store))
        self.assertEqual(recovered.data["events"][0]["status"], "approved")
        self.assertEqual(ContractStore(self.store).publish({**row, "proposal_id": "competing"}), "stale")
        self.assertEqual(ContractStore(self.store).lookup("__builtin_va_end", {"language": "other"})["status"],
                         "configuration_mismatch")

    def test_tool_roles_and_same_spelling_without_builtin_evidence(self):
        from stage2.contract_tools import ContractTools
        from stage2.materials import Materials
        from stage2.schedule import plan, task_description
        s = json.loads(self.stage1.read_bytes())
        output = self.root / "roles"
        output.mkdir()
        m = Materials(self.stage1, s, [], None, output)
        m.contract_log = ContractLog(output, ContractStore(self.store))
        s["graph"]["external_calls"][0].pop("kind")
        _, nodes, _, outgoing, incoming, deps = plan(s, {}, m)
        task = task_description(["trial"], nodes, outgoing, incoming, deps, {})
        tools = ContractTools(task, nodes, m)
        self.assertEqual([v["name"] for v in tools.calls.values()], ["__builtin_va_end"])
        writer, reviewer = m.reader(), m.reader()
        tools.attach(writer, "write")
        tools.attach(reviewer, "contract_review")
        self.assertNotIn("review_contract_change", writer.contract_actions)
        self.assertNotIn("propose_contract_change", reviewer.contract_actions)
        with self.assertRaises(ValueError):
            tools.lookup({"call_id": "nonexistent"})

    def test_unrelated_entry_does_not_change_requests(self):
        self.reject_first = False
        self.stage("seed")
        self.requests = []
        self.stage("before")
        before = self.requests
        log = ContractLog(self.root / "seed", ContractStore(self.store))
        seed, = log.data["events"]
        proposal = {**seed, "proposal_id": "unrelated",
                    "spec": {**SPEC, "id": "extensions/clang/hint",
                             "operations": {"__builtin_expect": {"name": "hint", "requires": "true",
                                                                  "ensures": "returns first operand"}}}}
        self.assertEqual(log.store.publish(proposal), "approved")
        self.requests = []
        self.stage("after")
        self.assertEqual(before, self.requests)

    def test_missing_and_unsupported_stays_unknown_without_proposal(self):
        self.abstain = True
        result = self.stage("abstain")
        draft, = result["functions"].values()
        self.assertEqual(draft["status"], "conditional")
        for check in draft["call_checks"].values():
            self.assertEqual((check["contract_lookup"], check["status"]), ("missing", "unknown"))
        self.assertEqual(self.decisions, [])

    def test_unknown_profile_stays_unknown(self):
        data = json.loads(self.stage1.read_text())
        del data["provenance"]["clang_default_target"]
        self.stage1.write_text(json.dumps(data))
        result = self.stage("unknown")
        self.assertEqual(result["status"], "partial")
        self.assertEqual(self.decisions, [])
        record, = result["functions"].values()
        self.assertTrue(all(c["status"] == "unknown" for c in record["call_checks"].values()))

    @unittest.skipUnless(os.environ.get("LST_RUN_GRAPH_TESTS") == "1", "requires pinned graph backend")
    def test_real_clang_calls_and_missing_end_path(self):
        target = self.root / "c"
        target.mkdir()
        source = target / "trial.c"
        source.write_text(self.unit.read_text().replace(" va_end(ap);", " if(last<0) return 0;\n va_end(ap);"))
        db = self.root / "commands.json"
        db.write_text(json.dumps([{"directory": str(target),"file":str(source),
                                   "arguments":["cc","-c",str(source)]}]))
        upstream = self.root / "real"
        s = analyze(target=target, compile_commands=db, output=upstream, configuration="Linux",
                    deps_root=os.environ["LST_DEPS_ROOT"])
        self.stage1 = upstream / "stage1.json"
        self.assertEqual({x["name"] for x in s["graph"]["external_calls"]}, set(SPEC["operations"]))
        self.reject_first = False
        result = self.stage("negative")
        record, = result["functions"].values()
        self.assertEqual(record["status"], "blocked")
        self.assertEqual({c["status"] for c in record["call_checks"].values()}, {"compatible", "conflict"})
        self.assertTrue(all("contract" in c for c in record["call_checks"].values()))
        source.write_text(self.unit.read_text())
        second = self.root / "paired"
        analyze(target=target, compile_commands=db, output=second, configuration="Linux",
                deps_root=os.environ["LST_DEPS_ROOT"])
        self.stage1 = second / "stage1.json"
        self.assertEqual(self.stage("positive")["status"], "completed")
        self.assertEqual(self.decisions, ["approve"])
