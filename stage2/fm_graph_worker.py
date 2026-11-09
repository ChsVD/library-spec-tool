"""Isolated adapter to the pinned, unmodified FM-Agent C graph backend."""
import argparse
import dataclasses
import json
import os
from pathlib import Path
import sqlite3
import sys


def main():
    p = argparse.ArgumentParser()
    p.add_argument("request")
    args = p.parse_args()
    request = json.loads(Path(args.request).read_text())
    project = Path(request["project"])
    sys.path.insert(0, request["fm_agent"])
    from src.languages import c, clang, c_indirect
    from src.languages.codegraph import CodeGraphExtractor, _node_fqn_map, _bare_function_name
    import tree_sitter_c
    from tree_sitter import Language, Parser

    extractor = CodeGraphExtractor.from_proj_dir(str(project))
    if extractor is None:
        raise RuntimeError("CodeGraph index missing/incomplete")
    db = sqlite3.connect(extractor._db)
    db.row_factory = sqlite3.Row
    fqns = _node_fqn_map(db.cursor(), ["c"])
    functions = []
    source_cache = {}
    parser = Parser(Language(tree_sitter_c.language()))
    for row in db.execute("SELECT * FROM nodes WHERE kind IN ('function','method') AND language='c' ORDER BY file_path,start_line"):
        row = dict(row)
        path = Path(row["file_path"])
        if path.is_absolute() or ".." in path.parts:
            raise ValueError("CodeGraph source outside snapshot")
        if path not in source_cache:
            source_cache[path] = (project / path).read_bytes()
        data = source_cache[path]
        lines = data.splitlines(keepends=True)
        start = sum(map(len, lines[:row["start_line"]-1])) + row["start_column"]
        end = sum(map(len, lines[:row["end_line"]-1])) + row["end_column"]
        body = data[start:end]
        tree = parser.parse(body)
        calls = []
        todo = [tree.root_node]
        while todo:
            node = todo.pop()
            if node.type == "call_expression":
                callee = node.child_by_field_name("function")
                calls.append({"expression": body[callee.start_byte:callee.end_byte].decode("utf-8"),
                              "line": row["start_line"] + node.start_point.row,
                              "column": node.start_point.column,
                              "syntax": callee.type})
            todo.extend(reversed(node.children))
        functions.append({"fqn": fqns[row["id"]], "symbol": _bare_function_name(row["name"]),
                          "file": str(path), "start": row["start_line"], "end": row["end_line"],
                          "start_byte": start, "end_byte": end, "code": body.decode("utf-8"),
                          "calls": calls, "syntax_error": tree.root_node.has_error})
    db.close()

    # Observe upstream results without changing its edge-resolution algorithm.
    coverage = set()
    original_edges = clang._clang_edges_from_asts
    def observed_edges(*a, **kw):
        edges, covered = original_edges(*a, **kw)
        coverage.update(covered)
        return edges, covered
    clang._clang_edges_from_asts = observed_edges
    parses = []
    diagnostics = []
    real_subprocess = clang.subprocess
    class ObservedProcess:
        def __getattr__(self, name):
            return getattr(real_subprocess, name)
        def run(self, *a, **kw):
            try:
                result = real_subprocess.run(*a, **kw)
            except (OSError, real_subprocess.SubprocessError) as exc:
                diagnostics.append({"command": a[0], "error": str(exc)})
                raise
            diagnostics.append({"command": a[0], "returncode": result.returncode,
                                "stderr": result.stderr})
            return result
    clang.subprocess = ObservedProcess()
    original_run = clang._run_clang_ast
    def observed_run(command, task, language, timeout, allow_errors=False):
        ast = original_run(command, task, language, timeout, allow_errors)
        parses.append({"source": str(task[0]), "partial_ast_allowed": allow_errors,
                       "ast_available": ast is not None})
        return ast
    clang._run_clang_ast = observed_run
    edges = c.call_edges(str(project))
    indirect_diagnostics = {}
    original_solve = c_indirect._Analysis.solve
    def observed_solve(analysis):
        result = original_solve(analysis)
        returned = {(s.caller, s.file, s.line) for s in result}
        indirect_diagnostics.update(
            unresolved_count=analysis.unresolved,
            omitted_sites=[{k: site.get(k) for k in ("caller","file","line","col","label","short_name")}
                           for site in analysis.sites if site and site.get("caller") is not None
                           and (site["caller"],site["file"],site["line"]) not in returned],
            lost_targets=[{"caller":k[0],"file":k[1],"line":k[2],"column":k[3],"names":sorted(v)}
                          for k,v in analysis.lost.items()])
        return result
    c_indirect._Analysis.solve = observed_solve
    sites = c.indirect_calls(str(project))
    result = {"functions": functions, "edges": edges or [],
              "indirect_sites": [dataclasses.asdict(s) for s in sites], "indirect_diagnostics": indirect_diagnostics,
              "clang_covered": sorted(coverage), "parses": parses, "diagnostics": diagnostics}
    Path(request["result"]).write_text(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
