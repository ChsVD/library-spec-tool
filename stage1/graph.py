"""Resolve graph identities, preserve backend evidence, and compute proof scope."""
from collections import defaultdict
import hashlib
import json
from pathlib import Path

from .inputs import owner


def layers(graph):
    """SCC condensation in caller-before-callee order (iterative, no recursion limit)."""
    selected = {k for k, v in graph['nodes'].items() if v['selected']}
    adj = {k: set() for k in selected}
    rev = {k: set() for k in selected}
    for e in graph['edges'].values():
        a, b = e['caller'], e['callee']
        if a in selected and b in selected:
            adj[a].add(b); rev[b].add(a)
    seen, order = set(), []
    for root in sorted(selected):
        stack = [(root, False)]
        while stack:
            node, done = stack.pop()
            if done:
                order.append(node); continue
            if node in seen: continue
            seen.add(node); stack.append((node, True))
            stack.extend((x, False) for x in sorted(adj[node], reverse=True) if x not in seen)
    groups, owners = [], {}
    for root in reversed(order):
        if root in owners: continue
        group, stack = [], [root]
        while stack:
            node = stack.pop()
            if node in owners: continue
            owners[node] = len(groups); group.append(node)
            stack.extend(rev[node] - owners.keys())
        groups.append(sorted(group))
    predecessors = {i: set() for i in range(len(groups))}
    for a in adj:
        for b in adj[a]:
            if owners[a] != owners[b]: predecessors[owners[b]].add(owners[a])
    result, remaining, done = [], set(predecessors), set()
    while remaining:
        ready = sorted(i for i in remaining if predecessors[i] <= done)
        result.append([groups[i] for i in ready]); done.update(ready); remaining.difference_update(ready)
    return result

def function_id(library, source, symbol, signature):
    identity = [library, source["path"], source["line"], source["column"], symbol, signature]
    return "fn-" + hashlib.sha256(json.dumps(identity).encode()).hexdigest()[:24]


def build_graph(raw, project, copies, failed_units):
    nodes, edges = {}, {}
    external, gaps = [], []
    declarations, definitions = {}, defaultdict(set)
    syntax_callers = set()
    failed_target = any(owner(Path(path), copies) == "target" for path in failed_units)
    reuse_index = {}

    def relative(location):
        path = Path(location["path"])
        library = owner(path, copies)
        if library:
            return library, {**location, "path": path.relative_to(copies[library]).as_posix()}
        return None, location

    def register(decl, status):
        library, source = relative(decl["location"])
        ident = function_id(library, source, decl["symbol"], decl["type"])
        nodes[ident] = {"id": ident, "library": library, "name": decl["name"],
                        "symbol": decl["symbol"], "type": decl["type"], "linkage": decl["linkage"],
                        "source": {**source, "end_line": decl["end_line"]},
                        "status": status, "selected": False}
        return ident

    def add_edge(caller, callee, location, evidence, kind):
        _, source = relative(location)
        key = (caller, callee)
        edge = edges.setdefault(key, {"caller": caller, "callee": callee, "callsites": []})
        site = {**source, "kind": kind, "evidence": evidence}
        if site not in edge["callsites"]:
            edge["callsites"].append(site)

    for unit in raw["units"]:
        for ast_id, decl in unit["declarations"].items():
            library, source = relative(decl["location"])
            if library and library != "target":
                ident = function_id(library, source, decl["symbol"], decl["type"])
                reuse_index[ident] = {**decl, "location": source, "id": ident, "library": library}
                reuse_index[ident].pop("previous", None)
            if not library or not decl["definition"]:
                continue
            ident = function_id(library, source, decl["symbol"], decl["type"])
            if ident not in nodes:
                register(decl, "definition")
            unit_library, unit_source = relative({"path": unit["source"]})
            unit_record = {"library": unit_library, **unit_source}
            compiled_in = nodes[ident].setdefault("translation_units", [])
            if unit_record not in compiled_in:
                compiled_in.append(unit_record)
            declarations[unit["source"], ast_id] = ident
            if decl["linkage"] == "external":
                definitions[decl["symbol"]].add(ident)

    # Preserve legacy lexical information for translation units that Clang did not parse.
    # Unconfirmed header and inactive C definitions stay in raw-graph.json.
    for entry in raw["functions"]:
        path = project / entry["file"]
        if str(path) not in failed_units or owner(path, copies) != "target":
            continue
        ident = register({"location": {"path": str(path), "line": entry["start"], "column": 0},
                          "end_line": entry["end"], "symbol": entry["symbol"], "name": entry["symbol"],
                          "type": None, "linkage": "unknown"}, "syntax_fallback")
        syntax_callers.add(ident)

    # Map upstream FQNs to a unique definition by file, symbol and source interval.
    by_source = defaultdict(list)
    for ident, node in nodes.items():
        by_source[copies[node["library"]] / node["source"]["path"], node["name"]].append(ident)
    fqns = {}
    for entry in raw["functions"]:
        matches = [ident for ident in by_source[project / entry["file"], entry["symbol"]]
                   if entry["start"] <= nodes[ident]["source"]["line"] <= entry["end"]]
        if len(matches) == 1:
            fqns[entry["fqn"]] = matches[0]

    for edge in raw["edges"]:
        caller, callee = fqns.get(edge["caller"]), fqns.get(edge["callee"])
        if caller in syntax_callers and callee and nodes[callee]["library"] == "target":
            span = edge.get("span", {})
            path = span.get("file") or str(copies["target"] / nodes[caller]["source"]["path"])
            add_edge(caller, callee, {"path": str(project / path), "line": span.get("start_line"),
                                     "column": span.get("start_col", 0)}, "legacy_syntax", "candidate")

    pending = defaultdict(list)
    for site in raw["indirect_sites"]:
        caller = fqns.get(site["caller"])
        if caller:
            for target in site["targets"]:
                if target in fqns and nodes[fqns[target]]["library"] == "target":
                    pending[caller, str(project / site["file"]), site["line"]].append(
                        (fqns[target], site["how"]))

    for unit in raw["units"]:
        decls = unit["declarations"]
        for call in unit["calls"]:
            caller = declarations.get((unit["source"], call["caller"]))
            if not caller:
                continue
            loc = call["location"]
            decl = decls.get(call["callee"])
            if not decl:
                for candidate, how in pending[caller, loc["path"], loc["line"]]:
                    add_edge(caller, candidate, loc, how, "indirect_candidate")
                gaps.append({"caller": caller, "location": relative(loc)[1], "reason": "unresolved_indirect_call",
                             "candidate_ids": sorted({ident for ident, _ in pending[caller, loc["path"], loc["line"]]})})
                continue
            chain = []
            cursor = decl
            ast_id = call["callee"]
            while cursor:
                chain.append((ast_id, cursor))
                ast_id = cursor["previous"]
                cursor = decls.get(ast_id)
            local = {declarations[unit["source"], key] for key, _ in chain if (unit["source"], key) in declarations}
            candidates = local or (definitions[decl["symbol"]] if decl["linkage"] == "external" else set())
            target_defs = {ident for ident in candidates if nodes[ident]["library"] == "target"}
            ref_decls = {library: item for _, item in chain
                         if (library := relative(item["location"])[0]) and library != "target"}
            if not candidates and len(ref_decls) == 1 and decl["linkage"] == "external" and not failed_target:
                # The resolved declaration comes from the supplied reference headers.
                # A failed target TU could hide a competing definition.
                item = next(iter(ref_decls.values()))
                candidates = {register(item, "reference_declaration")}
            if candidates:
                confirmed = set()
                for ident in sorted(candidates):
                    n = nodes[ident]
                    # Keep target definitions reachable even if declaration/type evidence is ambiguous.
                    if n["library"] == "target":
                        add_edge(caller, ident, loc, "clang_declaration", "direct" if len(candidates) == 1 else "candidate")
                        if len(candidates) == 1:
                            confirmed.add(ident)
                    elif len(candidates) == 1 and not target_defs and (
                            ident in local or (not failed_target and n["library"] in ref_decls and n["type"] == decl["type"])):
                        add_edge(caller, ident, loc, "clang_declaration", "direct")
                        confirmed.add(ident)
                if confirmed:
                    continue
            if not candidates and not ref_decls and decl["linkage"] == "external":
                external.append({"caller": caller, "location": relative(loc)[1], "name": decl["name"],
                                 "type": decl["type"], "declaration_library": relative(decl["location"])[0],
                                 "declaration": relative(decl["location"])[1]})
            else:
                gaps.append({"caller": caller, "location": relative(loc)[1], "reason": "unconfirmed_call_target",
                             "name": decl["name"], "candidate_ids": sorted(candidates)})

    def unique(records):
        return list({json.dumps(r, sort_keys=True): r for r in records}.values())

    return {"nodes": nodes, "edges": {f"e-{i}": edge for i, edge in enumerate(edges.values(), 1)},
            "reuse_index": list(reuse_index.values()), "external_calls": unique(external),
            "analysis_gaps": unique(gaps)}


def compute_scope(graph, entries):
    """Select every target definition or the conservative closure from entries."""
    nodes = graph["nodes"]
    target = {ident for ident, node in nodes.items() if node["library"] == "target"}
    if entries:
        roots = set()
        for entry in entries:
            matches = {i for i in target if entry in (i, nodes[i]["name"],
                       f"{nodes[i]['source']['path']}:{nodes[i]['name']}")}
            if len(matches) != 1:
                raise ValueError(f"entry must identify one target function: {entry} ({sorted(matches)})")
            roots.update(matches)
    else:
        roots = target
    adjacency = defaultdict(list)
    for edge in graph["edges"].values():
        adjacency[edge["caller"]].append(edge)
    reached, boundaries, work = set(), [], list(sorted(roots))
    # Follow known reference-internal edges only to find callbacks into the target.
    while work:
        ident = work.pop()
        if ident in reached:
            continue
        reached.add(ident)
        for edge in adjacency[ident]:
            callee = edge["callee"]
            if ident in target and callee not in target:
                boundaries.append(edge)
            work.append(callee)
    selected = reached & target
    for ident, node in nodes.items():
        node["selected"] = ident in selected
    projected = {**graph, "edges": dict(graph["edges"])}
    # Include known reference-mediated callbacks in SCC order and dependency structure.
    callback_edges = set()
    if reached - target:
        for ident in sorted(selected):
            todo = [e["callee"] for e in adjacency[ident] if e["callee"] not in target]
            visited = set()
            while todo:
                ref = todo.pop()
                if ref in visited:
                    continue
                visited.add(ref)
                for edge in adjacency[ref]:
                    callee = edge["callee"]
                    if callee in target:
                        callback_edges.add((ident, callee))
                    else:
                        todo.append(callee)
    for caller, callee in sorted(callback_edges):
        projected["edges"][caller, callee] = {"caller": caller, "callee": callee}
    groups = [group for layer in layers(projected) for group in layer]
    components = [{"id": f"scc-{i}", "functions": group} for i, group in enumerate(groups)]
    index = {ident: group["id"] for group in components for ident in group["functions"]}
    dependencies = sorted({(index[e["caller"]], index[e["callee"]]) for e in projected["edges"].values()
                           if e["caller"] in index and e["callee"] in index
                           and index[e["caller"]] != index[e["callee"]]})
    return {"mode": "entries" if entries else "whole_library", "entry_ids": sorted(roots) if entries else [],
            "function_ids": sorted(selected), "reached_ids": sorted(reached),
            "reuse_boundaries": sorted(boundaries, key=lambda e: (e["caller"], e["callee"])),
            "components": components, "component_edges": [list(edge) for edge in dependencies],
            "callback_dependencies": [{"caller": a, "callee": b} for a, b in sorted(callback_edges)]}
