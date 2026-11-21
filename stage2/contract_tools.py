"""Agent tools for looking up, proposing and independently reviewing builtin contracts."""
import json
from uuid import uuid4

from .contract_store import ID_PATTERN, checked_text
from .schedule import digest
from .storage import save


WRITE_GUIDE = """For each compiler builtin call below, use lookup_contract with call_id (or call_ids).
A lookup is evidence of the operation's identity, not proof that this use meets its prerequisites.
On missing or incorrect semantics you may use propose_contract_change with
{call_ids:[...],base_version:0,reason:"...",spec:{id:"stdlib/stdarg/va_list_lifecycle",
source:"normative document and section",operations:{"__builtin_name":{"name":"interface name",
"requires":"...","ensures":"..."}},checks:["cross-call obligations"]}}.
Use base_version 0 for creation or the exact current version for modification; preserve other bindings.
For implementation-specific operations use extensions/clang/<entry>. Restrict rules to supported
portable source semantics in the reported profile. Use reliable, specific authority. If evidence
is insufficient, leave unknown. A caller violating a valid rule is a call finding, not a rule edit.
Finish with the normal function draft. These tools are available individually outside read batches."""

DECISION_GUIDE = """Independently evaluate each proposed shared contract against its named authority,
applicability, original rule and source evidence. A local project's implementation alone cannot
establish a universal rule. Reject unsupported or overbroad semantics and caller-specific workarounds.
For each proposal invoke review_contract_change with proposal_id, decision ("approve" or "reject"),
and a specific reason. You may lookup_contract or use the read tools. Finish with report {}."""


def compiler_profile(materials, node):
    provenance = materials.compiler_info
    if not provenance.get("clang_version"):
        return None
    profiles = []
    for unit in node.get("translation_units", []):
        alias = materials.alias(unit["library"], unit["path"])
        args = materials.compile_args.get(alias)
        if not args:
            return None
        mode = provenance.get("clang_default_c_mode")
        target = provenance.get("clang_default_target")
        flags = []
        for i, arg in enumerate(args):
            if arg.startswith("@") or arg in ("-Xclang", "-cc1", "-Xarch_host") or arg.endswith("=native"):
                return None
            if arg.startswith(("-std=", "--std=")):
                mode = arg.split("=", 1)[1]
            elif arg == "-ansi":
                mode = "c90"
            elif arg in ("-target", "--target") and i + 1 < len(args):
                target = args[i + 1]
            elif arg.startswith(("--target=", "-target=")):
                target = arg.split("=", 1)[1]
            elif arg in ("-arch", "-march", "-mcpu", "-mtune", "-mabi", "-isysroot", "--sysroot"):
                if i + 1 >= len(args):
                    return None
                flags.extend([arg, args[i + 1]])
            elif arg.startswith(("--sysroot=", "-m", "-f", "-O", "-pedantic")):
                flags.append(arg)
        explicit_mode = any(a.startswith(("-std=", "--std=")) or a == "-ansi" for a in args)
        if not explicit_mode and target != provenance.get("clang_default_target"):
            return None
        if not mode or not target:
            return None
        profiles.append({"compiler": provenance["clang_version"], "language": mode,
                         "target": target, "options": flags})
    if profiles and all(p == profiles[0] for p in profiles):
        return profiles[0]
    return None


class ContractLog:
    def __init__(self, output, store):
        self.store = store
        self.path = output / "contract-changes.json"
        self.data = (json.loads(self.path.read_text()) if self.path.exists() else
                     {"run_id": uuid4().hex, "events": []})
        for row in self.data["events"]:
            if row["status"] == "publishing":
                row["status"] = store.publish(row)
        self.save()

    def save(self):
        self.data["approved_changes"] = sum(row["status"] == "approved" for row in self.data["events"])
        save(self.path, self.data)

    def propose(self, proposal):
        ident = digest([self.data["run_id"], proposal])
        existing = next((p for p in self.data["events"] if p["proposal_id"] == ident), None)
        if existing:
            return existing
        row = {**proposal, "proposal_id": ident, "status": "pending"}
        self.data["events"].append(row)
        self.save()
        return row

    def decide(self, row, decision, reason):
        if decision not in ("approve", "reject"):
            raise ValueError("decision must be approve or reject")
        checked_text(reason, "review reason")
        if row["status"] != "pending":
            return row["status"]
        row.update(review_reason=reason, status="publishing" if decision == "approve" else "rejected")
        self.save()
        if decision == "approve":
            row["status"] = self.store.publish(row)
            self.save()
        return row["status"]


class ContractTools:
    def __init__(self, task, nodes, materials):
        self.log = materials.contract_log
        self.calls = {}
        for key, call in task["outgoing"].items():
            detail = call.get("detail", {})
            if call["kind"] == "external" and detail.get("kind") == "compiler_builtin":
                self.calls[key] = {"name": detail["name"], "type": detail.get("type"), "location": call["location"],
                                   "caller": call["caller"], "profile": compiler_profile(materials, nodes[call["caller"]])}
        self.looked_up = {}
        self.proposals = {}

    def lookup(self, action):
        return self._lookup(action, pinned=False)

    def lookup_pinned(self, action):
        return self._lookup(action, pinned=True)

    def _lookup(self, action, pinned):
        ids = action.get("call_ids", [action.get("call_id")])
        if not isinstance(ids, list) or not ids or any(k not in self.calls for k in ids):
            raise ValueError("lookup needs builtin call IDs from this task")
        rules, calls = {}, {}
        for key in ids:
            c = self.calls[key]
            result = (self.looked_up[key] if pinned else self.log.store.lookup(c["name"], c["profile"]))
            self.looked_up[key] = result
            if result["status"] == "matched":
                rules[result["digest"]] = result["spec"]
            calls[key] = {"operation": c["name"], **{k: v for k, v in result.items() if k != "spec"}}
        return {"calls": calls, "rules": rules}

    def propose(self, action):
        ids = action.get("call_ids")
        if not isinstance(ids, list) or not ids or any(k not in self.looked_up for k in ids):
            raise ValueError("lookup the triggering call_ids before proposing a contract")
        selected = {k: self.calls[k] for k in ids}
        profile = selected[ids[0]]["profile"]
        if not profile or any(c["profile"] != profile for c in selected.values()):
            raise ValueError("a proposal requires one known compiler profile")
        spec = action["spec"]
        if not isinstance(spec, dict) or set(spec) != {"id", "source", "operations", "checks"}:
            raise ValueError("spec requires id, source, operations and checks")
        ident = checked_text(spec["id"], "id")
        if not ID_PATTERN.fullmatch(ident):
            raise ValueError("expected stdlib/<header>/<entry> or extensions/clang/<entry>")
        checked_text(spec["source"], "authority and section")
        if not isinstance(spec["checks"], list):
            raise ValueError("checks must be a list")
        for check in spec["checks"]:
            checked_text(check, "check")
        store = self.log.store
        head = store.index()["heads"].get(ident, {}).get(digest(profile), {})
        base = action.get("base_version")
        current = head.get("version", 0)
        old = (json.loads(store.revision(ident, digest(profile), current).read_text())["spec"]
               if current else None)
        if type(base) is not int or base != current:
            return {"status": "stale", "current_version": current, "current_spec": old}
        ops = spec["operations"]
        names = {c["name"] for c in selected.values()}
        previous = old["operations"] if old else {}
        if not isinstance(ops, dict) or set(ops) != names | previous.keys():
            raise ValueError("bind observed operations and retain existing bindings")
        for name, op in ops.items():
            if name not in names and op != previous[name]:
                raise ValueError("changed bindings require a triggering call")
            if not isinstance(op, dict) or set(op) != {"name", "requires", "ensures"}:
                raise ValueError("each operation needs name, requires and ensures")
            for k, v in op.items():
                checked_text(v, k)
        if old == spec:
            raise ValueError("proposal has no change")
        if any(self.looked_up[k].get("id", ident) != ident for k in ids):
            raise ValueError("modify the existing matched entry for these bindings")
        record = self.log.propose({"operation": "modify" if old else "add", "base_version": base,
                                   "proposed_version": base + 1, "profile": profile, "before": old,
                                   "spec": spec, "calls": selected, "reason": checked_text(action["reason"], "reason")})
        self.proposals[record["proposal_id"]] = record
        return {"proposal_id": record["proposal_id"], "status": record["status"]}

    @staticmethod
    def feedback(row):
        return {k: row.get(k) for k in ("proposal_id", "status", "review_reason", "spec")}

    def attach(self, reader, role):
        reader.contract_actions = {"lookup_contract": self.lookup}
        if role == "write":
            reader.contract_actions["propose_contract_change"] = self.propose
        elif role == "contract_review":
            reader.contract_actions["review_contract_change"] = self.review

    def review(self, action):
        row = self.proposals.get(action["proposal_id"])
        if row is None:
            raise ValueError("proposal is outside this review")
        status = self.log.decide(row, action["decision"], action["reason"])
        return {"status": status, "proposal_id": row["proposal_id"]}

    def finish_decisions(self, report, reader):
        if report != {}:
            raise ValueError("finish the contract decisions with an empty report")
        if any(row["status"] == "pending" for row in self.proposals.values()):
            raise ValueError("review each pending proposal before finishing")
        return report

    def require_lookups(self):
        if self.calls.keys() != self.looked_up.keys():
            raise ValueError("lookup each builtin call before finishing; call_ids can be queried together")
