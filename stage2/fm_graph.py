"""FM-Agent graph integration. Analysis snapshots never modify input sources."""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile

from .graph import digest, layers

BASE = Path(__file__).resolve().parents[1]
FM_COMMIT = "c552cd5ef25bd096178c7b06d3645dc3fd1e376e"
CODEGRAPH_VERSION = "1.6.2-fmagent.1"


def backend_identity(compile_commands=None):
    return {"backend": "fm-agent", "adapter_version": 1, "fm_agent_commit": FM_COMMIT,
            "codegraph_version": CODEGRAPH_VERSION,
            "adapter_sha256": digest([(BASE/"stage2/fm_graph.py").read_text(), (BASE/"stage2/fm_graph_worker.py").read_text()]),
            "python_requirements_sha256": hashlib.sha256((BASE/"scripts/graph-requirements.txt").read_bytes()).hexdigest(),
            "clang_version": subprocess.check_output(["clang", "--version"], text=True).splitlines()[0],
            "compile_commands_sha256": hashlib.sha256(Path(compile_commands).read_bytes()).hexdigest() if compile_commands else None,
            "default_configuration": "OpenSSL linux-x86_64 no-asm no-shared; otherwise explicit include paths"}


def checked(argv, cwd, log, env=None, timeout=600):
    with Path(log).open("w") as stream:
        process = subprocess.Popen([str(a) for a in argv], cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise RuntimeError("Graph analysis interrupted/timed out; see " + str(log))
        if code:
            raise RuntimeError(f"Graph analysis failed (exit {code}); see {log}")


def environment():
    fm = BASE / ".deps/FM-Agent"
    python = BASE / ".venv-graph/bin/python"
    cg = BASE / ".deps/codegraph/bin/codegraph"
    if not all(p.exists() for p in (fm, python, cg)) or not shutil.which("clang"):
        raise RuntimeError("FM-Agent graph environment missing; run bash scripts/setup_graph.sh inside WSL")
    commit = subprocess.check_output(["git", "-C", str(fm), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(fm), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    version = subprocess.check_output([str(cg), "--version"], text=True).strip()
    if commit != FM_COMMIT or dirty or version != CODEGRAPH_VERSION:
        raise RuntimeError("FM-Agent/CodeGraph differs from the pinned graph backend")
    return fm, python, cg


def build_graph(root, manifest, *, workspace=None, compile_commands=None):
    fm, python, cg = environment()
    root = Path(root).resolve(strict=True)
    if workspace is None:
        cache = BASE / ".cache/graphs"
        cache.mkdir(parents=True, exist_ok=True)
        workspace = Path(tempfile.mkdtemp(prefix="analysis-", dir=cache))
    else:
        workspace = Path(workspace).resolve()
        if workspace.is_relative_to(root):
            raise ValueError("analysis workspace must be outside input")
        workspace.mkdir(parents=True, exist_ok=False)
    if workspace.is_relative_to(root):
        raise ValueError("analysis workspace must be outside input")
    inventory = manifest.get("selection_inventory", {})
    selected_files = {f["path"] for f in inventory.get("files", [])
                      if f.get("status") not in ("excluded", "not_c_source")}
    selected_files.update(n["source"]["path"] for n in manifest["functions"])
    tops = {Path(f).parts[0] for f in selected_files}
    prefix = next(iter(tops)) if len(tops) == 1 and (root / next(iter(tops))).is_dir() else ""
    origin = root / prefix
    project = workspace / "project"
    # Refuse escaping links before copying; preserve internal links for build tools.
    for path in origin.rglob("*"):
        if path.is_symlink() and not path.resolve().is_relative_to(origin):
            raise ValueError("source symlink escapes analysis project: " + str(path))
    shutil.copytree(origin, project, symlinks=False,
                    ignore=shutil.ignore_patterns(".git", ".codegraph", "__pycache__"))
    env = dict(os.environ, CODEGRAPH_TELEMETRY="0", CLANG_COMMAND="clang", CLANG_TIMEOUT_SECONDS="120")
    env.pop("CLANG_COMPILE_COMMANDS", None)
    configuration = {"kind": "generated-analysis-commands", "proved_equivalent": False}
    if (project / "Configure").is_file() and (project / "Configurations").is_dir() and not compile_commands:
        checked(["perl", "Configure", "linux-x86_64", "no-asm", "no-shared"], project, workspace / "configure.log", env)
        checked(["make", "-j2", "build_generated"], project, workspace / "generated.log", env)
        configuration["openssl"] = ["linux-x86_64", "no-asm", "no-shared"]
    if compile_commands:
        commands = json.loads(Path(compile_commands).read_text())
        if not isinstance(commands, list) or not commands:
            raise ValueError("compile_commands must contain a nonempty JSON array")
        # Rewrite paths, never execute the compiler commands from the database.
        def rewrite(value):
            if isinstance(value, str):
                return value.replace(str(origin), str(project))
            if isinstance(value, list):
                return [rewrite(v) for v in value]
            if isinstance(value, dict):
                return {k: rewrite(v) for k, v in value.items()}
            return value
        commands = rewrite(commands)
        for command in commands:
            if not isinstance(command, dict) or not command.get("file") or not command.get("directory") or not (command.get("arguments") or command.get("command")):
                raise ValueError("invalid compilation database entry")
            directory = Path(command["directory"])
            source = Path(command["file"])
            source = source if source.is_absolute() else directory / source
            if not directory.is_absolute() or not directory.is_relative_to(project) or not source.resolve().is_relative_to(project):
                raise ValueError("compilation database source/directory must map into project snapshot")
            if not source.is_file():
                raise ValueError("compilation database references missing source")
        configuration["kind"] = "supplied-compile-commands"
    else:
        include_dirs = [project, project / "include", project / "crypto", project / "crypto/bn"]
        commands = []
        for name in sorted(selected_files):
            relative = Path(name).relative_to(prefix) if prefix else Path(name)
            source = project / relative
            if source.suffix.lower() == ".c":
                commands.append({"file": str(source), "directory": str(project),
                                 "arguments": ["clang", "-DOPENSSL_BUILDING_OPENSSL"] +
                                 [f"-I{d}" for d in include_dirs if d.is_dir()] + ["-c", str(source)]})
        configuration["warning"] = "Analysis configuration only; not the complete upstream build matrix"
    (project / "compile_commands.json").write_text(json.dumps(commands, indent=2))
    configuration["commands_sha256"] = hashlib.sha256((project / "compile_commands.json").read_bytes()).hexdigest()
    checked([cg, "init", "-y", project], project, workspace / "codegraph.log", env, timeout=1200)
    request = {"project": str(project), "fm_agent": str(fm), "result": str(workspace / "raw-graph.json")}
    (workspace / "request.json").write_text(json.dumps(request))
    checked([python, BASE / "stage2/fm_graph_worker.py", workspace / "request.json"],
            fm, workspace / "backend.log", env, timeout=3600)
    raw = json.loads((workspace / "raw-graph.json").read_text())
    graph = adapt(root, manifest, raw, prefix)
    graph["analysis"] = {**backend_identity(compile_commands), "workspace": str(workspace),
                         "configuration": configuration, "clang_covered": raw["clang_covered"],
                         "parses": raw["parses"], "diagnostics_file": str(workspace / "raw-graph.json"),
                         "clang_version": subprocess.check_output(["clang", "--version"], text=True).splitlines()[0],
                         "limits": ["Unverified candidate graph, not a soundness or completeness guarantee",
                                    "Inactive preprocessor variants and unparsed translation units use syntax fallback",
                                    "Indirect analysis is context-insensitive, field-based and bounded by upstream iteration limits",
                                    "Partial ASTs may be used by upstream indirect-call analysis"]}
    for node in graph["nodes"].values():
        node["configuration"] += "；依赖图分析配置：" + json.dumps({k:v for k,v in configuration.items() if k != "commands_sha256"}, ensure_ascii=False)
    (workspace / "analysis.json").write_text(json.dumps(graph["analysis"], ensure_ascii=False, indent=2))
    return graph


def adapt(root, manifest, raw, prefix=""):
    inventory = manifest.get("selection_inventory", {})
    selection = inventory.get("selection")
    files = {f["path"] for f in inventory.get("files", []) if f.get("status") not in ("excluded", "not_c_source")}
    originals = manifest["functions"]
    by_location = {(n["source"]["path"], n["symbol"], n["source"]["start"]): n for n in originals}
    nodes = {}; lookup = {}; indexed = {}; unknown = []; edges = {}
    covered = set(raw["clang_covered"])
    for f in raw["functions"]:
        path = str(Path(prefix) / f["file"])
        indexed[f["fqn"]] = {**f, "path": path}
        old = by_location.get((path, f["symbol"], f["start"]))
        # V1 is an explicit function whitelist; V2 is an approved file scope.
        if not old and not (selection and path in files):
            continue
        if old:
            node = copy.deepcopy(old)
        else:
            slug = re.sub("[^a-z0-9_-]", "-", f["symbol"].lower())[:42]
            ident = slug + "-" + hashlib.sha256(f"{path}:{f['start']}:{f['symbol']}".encode()).hexdigest()[:12]
            if ident in nodes: ident += "-" + digest(f["fqn"])[:8]
            node = {"id": ident, "symbol": f["symbol"],
                    "source": {"path": path, "start": f["start"], "end": f["end"]},
                    "module_id": selection["module_id"], "group_id": selection["id"],
                    "configuration": selection["configuration"],
                    "materials": selection["materials"]}
        node.pop("code_offsets", None)
        node.update(code=f["code"], selected=True, status="pending", spec=None, fqn=f["fqn"])
        nodes[node["id"]] = node; lookup[f["fqn"]] = node["id"]
        if f["fqn"] not in covered:
            unknown.append({"caller": node["id"], "reason": "Not covered by successful Clang AST; syntax fallback/configuration unknown"})
        if f["syntax_error"]:
            unknown.append({"caller": node["id"], "reason": "Tree-sitter reports a syntax error in indexed function"})
    # Keep legacy inventory discoveries that CodeGraph missed; do not silently drop scope.
    for old in originals:
        if old["id"] in nodes: continue
        node = copy.deepcopy(old); src = node["source"]
        text = (Path(root) / src["path"]).read_text()
        offsets = node.get("code_offsets")
        code = text[offsets["start"]:offsets["end"]] if offsets else "\n".join(text.splitlines()[src["start"]-1:src["end"]])
        node.update(code=code, selected=True, status="pending", spec=None)
        nodes[node["id"]] = node
        unknown.append({"caller": node["id"], "reason": "Selected definition missing from CodeGraph; dependencies unknown"})

    def add(caller, callee, evidence, span, label=None):
        if caller not in lookup: return
        caller_id = lookup[caller]
        if callee not in lookup:
            unknown.append({"caller": caller_id, "callee_fqn": callee, "source": span,
                            "reason": "Dependency outside approved function scope or not indexed", "evidence": evidence,
                            "target_source": {k:indexed[callee][k] for k in ("path","start","end")} if callee in indexed else None})
            return
        callee_id = lookup[callee]; key = "e-" + digest([caller_id, callee_id])[:16]
        edge = edges.setdefault(key, {"id": key, "caller": caller_id, "callee": callee_id,
                                      "symbol": nodes[callee_id]["symbol"], "certainty": "static_analysis_candidate",
                                      "requirements": [], "callsites": [], "evidence": []})
        if evidence not in edge["evidence"]: edge["evidence"].append(evidence)
        source_path = str(Path(prefix) / span.get("file", indexed[caller]["file"]))
        line = span.get("start_line", span.get("line"))
        context = {"source": {"path": source_path, "start": line, "end": line},
                   "expression": label, "span": span,
                   "note": "Candidate dependency; call-site conditions and configuration require review"}
        if line and (Path(root) / source_path).is_file():
            lines = (Path(root) / source_path).read_text().splitlines()
            first = max(0, line-4); last = min(len(lines), line+4)
            context["source"].update(start=first+1, end=last)
            context["code"] = "\n".join(lines[first:last])
        if context not in edge["callsites"]: edge["callsites"].append(context)

    accounted = set()
    for e in raw["edges"]:
        span = e.get("span", {})
        evidence = "codegraph:" + e["synthesized"] if e.get("synthesized") else ("clang" if e["caller"] in covered else "codegraph")
        add(e["caller"], e["callee"], evidence, span)
        accounted.add((e["caller"], span.get("start_line"), indexed.get(e["callee"], {}).get("symbol")))
    for site in raw["indirect_sites"]:
        if site["caller"] not in lookup: continue
        span = {"file": site["file"], "start_line": site["line"]}
        # Retain even resolved sites as uncertain dispatch, including provenance.
        unknown.append({"caller": lookup[site["caller"]], "reason": "Indirect dispatch candidate set is not guaranteed complete",
                        "indirect_site": site})
        for target in site["targets"]:
            add(site["caller"], target, "indirect:" + site["how"], span, site["label"])
        if site["targets"]: accounted.add((site["caller"], site["line"], site["label"]))
    diagnostics = raw.get("indirect_diagnostics", {})
    for site in diagnostics.get("omitted_sites", []):
        if site["caller"] in lookup:
            item = {"caller": lookup[site["caller"]], "reason": "Upstream indirect analysis omitted a call site without indexed candidate targets",
                    "indirect_site": site}
            if item not in unknown: unknown.append(item)
    for site in diagnostics.get("lost_targets", []):
        if site["caller"] in lookup:
            unknown.append({"caller": lookup[site["caller"]], "reason": "Upstream indirect targets missing from CodeGraph index",
                            "indirect_site": site})
    for fqn, ident in lookup.items():
        for call in indexed[fqn]["calls"]:
            if (fqn, call["line"], call["expression"]) not in accounted:
                unknown.append({"caller": ident, "symbol": call["expression"], "source": {"path": indexed[fqn]["path"], "start": call["line"]},
                                "reason": "Syntactic call site without resolved backend target; may be external, macro, indirect or inactive"})
    graph = {"nodes": nodes, "edges": edges, "unknown_calls": unknown,
             "inventory_gaps": inventory.get("gaps", []),
             "status": "unverified_reference_graph",
             "method": "Pinned FM-Agent: CodeGraph inventory + Clang direct edges with CodeGraph fallback + C indirect value flow"}
    graph["layers"] = layers(graph)
    graph["components"] = [{"id": "scc-" + str(k), "members": g}
                           for k, g in enumerate(g for layer in graph["layers"] for g in layer)]
    return graph
