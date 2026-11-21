"""Module-free stage-one entry point."""
import json
import os
from pathlib import Path
import subprocess

from .backend import BASE, CODEGRAPH_VERSION, FM_COMMIT, checked, environment
from .graph import build_graph, compute_scope
from .inputs import compilation_units, owner, prepare_snapshot, read_inputs, sha256


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def analyze(*, target, compile_commands, output, configuration, entries=(), reuse_libraries=None,
            deps_root=BASE):
    """Return the JSON-compatible stage-one result and write it to a new run directory."""
    if not isinstance(configuration, str) or not configuration.strip():
        raise ValueError("configuration must describe the platform and architecture")
    if isinstance(entries, str) or not all(isinstance(item, str) and item.strip() for item in entries):
        raise ValueError("entries must contain valid function selectors")
    output = Path(output).resolve()
    roots, databases, references = read_inputs(target, compile_commands, reuse_libraries)
    if any(output.is_relative_to(root) for root in roots.values()):
        raise ValueError("output must be outside all input roots")
    units = compilation_units(databases, roots)
    fm, python, codegraph = environment(Path(deps_root).resolve())
    clang_version = subprocess.check_output(["clang", "--version"], text=True).splitlines()[0]
    target_triple = subprocess.check_output(["clang", "-dumpmachine"], text=True).strip()
    macros = subprocess.check_output(["clang", "-dM", "-E", "-x", "c", "-"], input="", text=True)
    std_version = next((line.split()[-1] for line in macros.splitlines()
                        if line.startswith("#define __STDC_VERSION__ ")), None)
    default_mode = {"199901L": "gnu99", "201112L": "gnu11", "201710L": "gnu17",
                    "202311L": "gnu23"}.get(std_version)
    if default_mode and "#define __STRICT_ANSI__ " in macros:
        default_mode = default_mode.replace("gnu", "c")
    output.mkdir(parents=True, exist_ok=False)
    project = output / "project"
    try:
        copies = prepare_snapshot(project, roots, units)
        snapshot = [{"path": path.relative_to(project).as_posix(), "sha256": sha256(path)}
                    for path in sorted(project.rglob("*")) if path.is_file()]
        env = dict(os.environ, CODEGRAPH_TELEMETRY="0", CLANG_COMMAND="clang", CLANG_TIMEOUT_SECONDS="120")
        env.pop("CLANG_COMPILE_COMMANDS", None)
        env.pop("CPATH", None)
        env.pop("C_INCLUDE_PATH", None)
        checked([codegraph, "init", "-y", project], project, output / "codegraph.log", env, timeout=1200)
        raw_path = output / "raw-graph.json"
        request = output / "backend-request.json"
        write_json(request, {"project": str(project), "fm_agent": str(fm), "result": str(raw_path)})
        checked([python, Path(__file__).with_name("fm_graph_worker.py"), request],
                fm, output / "backend.log", env, timeout=3600)
        raw = json.loads(raw_path.read_text())
        parsed = {r["source"] for r in raw["units"]}
        coverage = []
        failed = set()
        for source in sorted(units):
            library = owner(source, roots)
            relative = source.relative_to(roots[library])
            mapped = str(copies[library] / relative)
            if mapped not in parsed:
                failed.add(mapped)
            coverage.append({"library": library, "path": relative.as_posix(),
                             "status": "parsed" if mapped in parsed else "analysis_parse_failed"})

        graph = build_graph(raw, project, copies, failed)
        scope = compute_scope(graph, entries)
        reached = set(scope["reached_ids"])
        relevant_gaps = [gap for gap in graph["analysis_gaps"] if gap["caller"] in reached]
        # A failed TU can contain a reachable definition not visible to the analyzer.
        parse_gaps = [item for item in coverage if item["status"] != "parsed"]
        status = "partial_analysis" if relevant_gaps or parse_gaps else "analysis_completed"
        result = {
            "schema_version": 1,
            "status": status,
            "configuration": configuration,
            "libraries": {name: {"source_root": str(root), "snapshot_root": copies[name].relative_to(output).as_posix(),
                                  **references.get(name, {"version": None, "materials": []})}
                          for name, root in roots.items()},
            "graph": graph, "scope": scope,
            "coverage": {
                "translation_units": coverage,
                "out_of_configuration_sources": [
                    {"library": name, "path": source.relative_to(root).as_posix()}
                    for name, root in roots.items() for source in sorted(root.rglob("*.c"))
                    if source.resolve() not in units and owner(source.resolve(), roots) == name
                ],
                "scoped_analysis_gaps": relevant_gaps,
                "scoped_external_calls": [call for call in graph["external_calls"] if call["caller"] in reached],
            },
            "provenance": {
                "fm_agent_commit": FM_COMMIT, "codegraph_version": CODEGRAPH_VERSION, "clang_version": clang_version,
                "clang_default_c_mode": default_mode, "clang_default_target": target_triple,
                "databases": [{"path": str(path), "sha256": sha256(path)} for path in databases],
                "snapshot_files": snapshot,
                "raw_graph": "raw-graph.json",
                "adapter_files": {path.name: sha256(path) for path in sorted(Path(__file__).parent.glob("*.py"))},
            },
        }
        write_json(output / "stage1.json", result)
        return result
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as exc:
        write_json(output / "failure.json", {"status": "stage1_failed", "message": str(exc)})
        raise
