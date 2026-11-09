"""Static scope/cost queries for one function-selection session."""
import copy
import json
from dataclasses import dataclass, asdict
from stage1.reader import Reader
from stage2.graph import digest, layers
from stage2.demand_scope import plan_graph, _ids
from stage3.read_materials import SourcePreparation


@dataclass(frozen=True)
class Limits:
    max_targets: int = 12
    max_generation: int = 40
    max_material_chars: int = 120000

    def __post_init__(self):
        if any(type(v) is not int or v < 1 for v in asdict(self).values()):
            raise ValueError("Selection limits must be positive integers")


class ScopeTools:
    def __init__(self, root, graph, limits=Limits()):
        self.graph = graph
        self.limits = limits
        full = copy.deepcopy(graph)
        for n in full["nodes"].values():
            n["selected"] = True
        self.components = sorted([sorted(c) for layer in layers(full) for c in layer])
        self.owner = {n: set(c) for c in self.components for n in c}
        self.adj = {n: set() for n in graph["nodes"]}
        self.rev = {n: set() for n in graph["nodes"]}
        for e in graph["edges"].values():
            self.adj[e["caller"]].add(e["callee"])
            self.rev[e["callee"]].add(e["caller"])
        self.preparation = SourcePreparation(root)
        self.cache = {}

    def describe(self, ids):
        return [{"id": i, "symbol": self.graph["nodes"][i]["symbol"],
                 "source": self.graph["nodes"][i]["source"]} for i in ids]

    @staticmethod
    def page(rows, offset):
        if type(offset) is not int or offset < 0:
            raise ValueError("offset must be a nonnegative integer")
        return {"items": rows[offset:offset+10], "total": len(rows),
                "next_offset": offset+10 if offset+10 < len(rows) else None}

    def frontier(self, offset=0):
        # Unknown calls do not disappear merely because no known edge leaves an SCC.
        rows = []
        for c in self.components:
            if any(self.adj[n] - set(c) for n in c):
                continue
            rows.append({"members": self.describe(c),
                "unknown_call_count": sum(u.get("caller") in c for u in self.graph.get("unknown_calls", [])),
                "status": "no_known_outgoing_edges_not_proof_ready"})
        result = self.page(rows, offset)
        result["inventory_gap_count"] = len(self.graph.get("inventory_gaps", []))
        return result

    def callers(self, targets, offset=0):
        plan = self.assess(targets)["plan"]
        group = set(plan["target_ids"])
        callers = sorted(set().union(*(self.rev[n] for n in group)) - group)
        return self.page(self.describe(callers), offset)

    def assess(self, targets):
        _ids(targets, self.graph["nodes"], "target_ids", True)
        key = tuple(sorted(targets))
        if key in self.cache:
            return self.cache[key]
        plan = plan_graph(self.graph, list(key))
        nodes = [self.graph["nodes"][i] for i in plan["generation_ids"]]
        pack = self.preparation.prepare(nodes)
        # Union original source ranges: repeated callees and shared macro/type lines count once.
        intervals = {}
        for ref in [n["source"] for n in nodes] + pack["source_fragments"]:
            intervals.setdefault(ref["path"], []).append((ref["start"], ref["end"]))
        materials, missing = [], []
        for path, ranges in sorted(intervals.items()):
            try:
                lines, sha, _, _ = self.preparation.file(path)
                merged = []
                for start, end in sorted(ranges):
                    if not 1 <= start <= end <= len(lines):
                        raise ValueError("source interval outside file")
                    if merged and start <= merged[-1][1]+1:
                        merged[-1][1] = max(merged[-1][1], end)
                    else:
                        merged.append([start, end])
                for start, end in merged:
                    materials.append({"path": path, "start": start, "end": end,
                        "sha256": sha, "text": "\n".join(lines[start-1:end])})
            except (ValueError, OSError, UnicodeError) as exc:
                missing.append({"path": path, "reason": str(exc)})
        chars = len(json.dumps(materials, ensure_ascii=False))
        counts = {"targets": len(plan["target_ids"]), "demand_callers": len(plan["demand_ids"]),
                  "generation": len(plan["generation_ids"]), "known_material_chars": chars}
        exceeded = [name for name, value, limit in [
            ("targets", counts["targets"], self.limits.max_targets),
            ("generation", counts["generation"], self.limits.max_generation),
            ("known_material_chars", chars, self.limits.max_material_chars)] if value > limit]
        result = {"plan": plan, "assessment_id": digest({"graph": digest(self.graph),
                    "targets": key, "limits": asdict(self.limits)}),
            "counts": counts, "limits": asdict(self.limits),
            "exceeded": exceeded, "within_limits": not exceeded and not missing,
            "missing_source": missing, "material_unknowns": pack["unknowns"],
            "unknown_call_count": plan["unknown_call_count"],
            "inventory_gap_count": len(plan["inventory_gaps"]),
            "material_status": "missing" if missing else "unknown" if
                pack["unknowns"] or plan["unknown_call_count"] or plan["inventory_gaps"] else "located_known_sources",
            "cost_basis": "Unique function source and statically located type/macro ranges for ALL generation_ids, serialized as JSON characters. Not tokens or a future stage3 prompt size.",
            "limitations": "No verified-contract matching: drafts never count as proved dependencies. Missing calls/includes remain unknown. Future specs, reference reading, total tokens, time and proof difficulty are not predicted."}
        self.cache[key] = result
        return result

    def evaluate(self, targets, baseline=None):
        current = self.assess(targets)
        before = set(self.assess(baseline)["plan"]["target_ids"]) if baseline else set()
        added = sorted(set(current["plan"]["target_ids"]) - before)
        result = {k:v for k,v in current.items() if k not in ("plan", "material_unknowns", "missing_source")}
        result.update(new_target_count=len(added), new_dependency_count=len(set(added)-set(targets)),
                      new_target_ids=added[:40], new_target_ids_truncated=len(added)>40,
                      material_unknown_count=len(current["material_unknowns"]),
                      missing_source_count=len(current["missing_source"]),
                      note="Use scope_details for full membership and missing/unknown records. Limits are batch workload caps, not a proof of material sufficiency.")
        return result

    def details(self, targets, section, offset=0):
        value = self.assess(targets)
        if section in ("target_ids", "demand_ids", "context_ids"):
            rows = self.describe(value["plan"][section])
        elif section in ("material_unknowns", "missing_source"):
            rows = value[section]
        elif section == "unknown_calls":
            keep = set(value["plan"]["generation_ids"])
            rows = [u for u in self.graph.get("unknown_calls", []) if u.get("caller") in keep]
        elif section == "inventory_gaps":
            rows = value["plan"]["inventory_gaps"]
        else:
            raise ValueError("unknown scope_details section")
        return self.page(rows, offset)


class SelectionReader(Reader):
    extra_material_tools = {"candidate_frontier", "direct_callers", "evaluate_group", "scope_details"}

    def __init__(self, root, log, scope):
        super().__init__(root, log)
        self.scope = scope

    def execute(self, action):
        op = action.get("tool")
        if op not in ("candidate_frontier", "direct_callers", "evaluate_group", "scope_details"):
            return super().execute(action)
        try:
            targets = action.get("target_ids")
            offset = action.get("offset", 0)
            if op == "candidate_frontier":
                value = self.scope.frontier(offset)
            elif op == "direct_callers":
                value = self.scope.callers(targets, offset)
            elif op == "evaluate_group":
                value = self.scope.evaluate(targets, action.get("baseline_target_ids"))
            else:
                value = self.scope.details(targets, action.get("section"), offset)
            if len(json.dumps(value, ensure_ascii=False)) > 24000:
                value = {"error": "Result exceeds 24000 characters; use a smaller group or inspect graph diagnostics outside this session. Nothing truncated silently."}
        except (KeyError, TypeError, ValueError, OSError, UnicodeError) as exc:
            value = {"error": str(exc)}
        with self.log.open("a", encoding="utf-8") as f:
            f.write(json.dumps({"action": action, "result": value}, ensure_ascii=False)+"\n")
        return value
