"""Stage-one project inputs and a private source copy for the graph backend."""
import hashlib
import json
from pathlib import Path
import re
import shlex
import shutil


def read_inputs(target, database, reuse_file=None):
    target = Path(target).resolve(strict=True)
    if not target.is_dir():
        raise ValueError("target must be a source directory")
    roots = {"target": target}
    databases = [Path(database).resolve(strict=True)]
    references = {}
    if reuse_file:
        config = Path(reuse_file).resolve(strict=True)
        items = json.loads(config.read_text(encoding="utf-8"))
        if not isinstance(items, list):
            raise ValueError("reuse libraries must be a JSON array")
        for item in items:
            if not isinstance(item, dict) or set(item) - {"id", "root", "compile_commands", "materials", "version"}:
                raise ValueError("invalid reuse library record")
            name = item.get("id")
            if not isinstance(name, str) or not re.fullmatch(r"[a-z][a-z0-9_-]*", name) or name in roots:
                raise ValueError("reuse library id must be unique and lowercase")
            if not isinstance(item.get("root"), str) or not item["root"]:
                raise ValueError(f"missing source directory for reuse library {name}")
            root = (config.parent / item["root"]).resolve(strict=True)
            if not root.is_dir() or root in roots.values() or target.is_relative_to(root):
                raise ValueError("reuse library requires a distinct source directory outside or inside target")
            roots[name] = root
            paths = item.get("materials", [])
            if not isinstance(paths, list) or not all(isinstance(path, str) for path in paths):
                raise ValueError(f"materials must be a list of paths for {name}")
            version = item.get("version")
            if version is not None and (not isinstance(version, str) or not version.strip()):
                raise ValueError(f"invalid version for reuse library {name}")
            references[name] = {"version": version,
                                "materials": [str((config.parent / path).resolve(strict=True)) for path in paths]}
            if "compile_commands" in item:
                databases.append((config.parent / item["compile_commands"]).resolve(strict=True))
    return roots, list(dict.fromkeys(databases)), references


def owner(path, roots):
    return next((name for name, root in sorted(roots.items(), key=lambda item: -len(item[1].parts))
                 if path.is_relative_to(root)), None)


def compilation_units(databases, roots):
    units = {}
    for database in databases:
        entries = json.loads(database.read_text(encoding="utf-8-sig"))
        if not isinstance(entries, list) or not entries:
            raise ValueError(f"empty or invalid compilation database: {database}")
        for item in entries:
            if (not isinstance(item, dict) or not isinstance(item.get("file"), str)
                    or not isinstance(item.get("directory"), str)):
                raise ValueError(f"invalid compilation database record in {database}")
            directory = Path(item["directory"])
            if not directory.is_absolute():
                directory = database.parent / directory
            directory = directory.resolve()
            source = (directory / item["file"]).resolve()
            if source.suffix != ".c" or owner(source, roots) is None:
                continue
            if not directory.is_dir() or not source.is_file():
                raise ValueError(f"missing compilation unit or working directory: {source}")
            args = item.get("arguments")
            if args is None and isinstance(item.get("command"), str):
                args = shlex.split(item["command"])
            if not isinstance(args, list) or not args or not all(isinstance(arg, str) for arg in args):
                raise ValueError(f"invalid compiler arguments for {source}")
            unit = {"directory": directory, "file": source, "arguments": args}
            if source in units and units[source] != unit:
                raise ValueError(f"multiple compiler configurations for {source}; select one before analysis")
            units[source] = unit
    if not any(owner(source, roots) == "target" for source in units):
        raise ValueError("compilation database contains no target .c translation units")
    return units


def prepare_snapshot(project, roots, units):
    """Copy each source tree once; map nested reuse roots inside the target copy."""
    copies = {}
    for name, root in sorted(roots.items(), key=lambda item: len(item[1].parts)):
        parent = owner(root, {key: roots[key] for key in copies})
        if parent:
            copies[name] = copies[parent] / root.relative_to(roots[parent])
            continue
        # CodeGraph skips directories named "target", "build", etc. Keep logical
        # library IDs separate from their on-disk names (including reuse IDs).
        dest = project / ("lib-" + name)
        for path in root.rglob("*"):
            if path.is_symlink() and not path.resolve().is_relative_to(root):
                raise ValueError(f"source symlink escapes project root: {path}")
        shutil.copytree(root, dest, ignore=shutil.ignore_patterns(".git", ".codegraph", "__pycache__"))
        copies[name] = dest

    pattern = re.compile("|".join(
        re.escape(str(root)) + r"(?=/|$)" for root in sorted(roots.values(), key=lambda p: -len(str(p)))
    ))
    mapped = {str(root): str(copies[name]) for name, root in roots.items()}
    def remap(value):
        return pattern.sub(lambda match: mapped[match[0]], str(value))

    commands = []
    for source, unit in sorted(units.items()):
        directory = unit["directory"]
        args = unit["arguments"]
        # Normalize the source argument when a build directory is outside the snapshot.
        normalized = [args[0]]
        for arg in args[1:]:
            if arg and not arg.startswith("-") and (directory / arg).resolve() == source:
                arg = str(source)
            normalized.append(remap(arg))
        commands.append({"file": remap(source), "directory": remap(directory), "arguments": normalized})
    (project / "compile_commands.json").write_text(json.dumps(commands, indent=2), encoding="utf-8")
    return copies


def sha256(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()
