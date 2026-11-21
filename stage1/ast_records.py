"""Extract source identities and direct call evidence from Clang JSON ASTs."""
from bisect import bisect_right
from functools import lru_cache
from pathlib import Path


@lru_cache(maxsize=512)
def newline_offsets(file):
    try:
        return tuple(i for i, byte in enumerate(Path(file).read_bytes()) if byte == 10)
    except OSError:
        return ()


def position(loc, current, directory):
    loc = loc.get("expansionLoc", loc.get("spellingLoc", loc))
    file = loc.get("file")
    if file and not file.startswith("<"):
        current = str((directory / file).resolve())
    line = loc.get("line")
    if line is None and current and "offset" in loc:
        line = bisect_right(newline_offsets(current), loc["offset"] - 1) + 1
    if current and line:
        return {"path": current, "line": line, "column": loc.get("col", 0)}
    return None


def collect(ast, source, directory, call_target):
    declarations, calls = {}, []
    def walk(node, file, caller):
        loc = position(node.get("loc", {}), file, directory)
        if loc:
            file = loc["path"]
        children = node.get("inner", [])
        if (node.get("kind") == "FunctionDecl" and node.get("isImplicit")
                and node.get("name", "").startswith("__builtin_")
                and any(child.get("kind") == "BuiltinAttr" for child in children)):
            declarations[node["id"]] = {"compiler_builtin": True, "name": node["name"],
                                        "type": node.get("type", {}).get("qualType")}
        if node.get("kind") == "FunctionDecl" and loc and not node.get("isImplicit"):
            ident = node["id"]
            previous = declarations.get(node.get("previousDecl"), {})
            body = any(child.get("kind") == "CompoundStmt" for child in children)
            end = position(node.get("range", {}).get("end", {}), file, directory)
            declarations[ident] = {
                "name": node["name"], "symbol": node.get("mangledName", node["name"]),
                "type": node.get("type", {}).get("qualType"),
                "linkage": "internal" if node.get("storageClass") == "static" or
                previous.get("linkage") == "internal" else "external",
                "location": loc, "end_line": end["line"] if end and end["path"] == file else loc["line"],
                "definition": body,
                "previous": node.get("previousDecl"),
            }
            caller = ident if body else None
        if caller and node.get("kind") == "CallExpr":
            site = position(node.get("range", {}).get("begin", {}), file, directory)
            if site:
                calls.append({"caller": caller, "callee": call_target(node), "location": site})
        sibling_file = file
        for child in children:
            sibling_file = walk(child, sibling_file, caller)
        return file if node.get("kind") == "FunctionDecl" else sibling_file

    walk(ast, str(source), None)
    return {"source": str(source), "declarations": declarations, "calls": calls}
