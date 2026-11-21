"""Versioned source and contract inputs, with in-memory read evidence."""
import json
from pathlib import Path

from stage1.inputs import sha256
from .reader import Reader


class MaterialReadError(ValueError):
    """A task's required material cannot be delivered."""


class Materials:
    def __init__(self, stage1_path, stage1, background, contracts, output):
        self.root = stage1_path.parent
        self.definitions = {}
        self.compiler_info = stage1["provenance"]
        self.contract_log = None
        self.paths = {}
        self.digests = {}
        self.reference_paths = {}
        self.background = []
        self.contracts = {}
        for item in stage1["provenance"]["snapshot_files"]:
            alias = item["path"]
            path = (self.root / "project" / alias).resolve(strict=True)
            if not path.is_relative_to(self.root / "project"):
                raise ValueError(f"snapshot path escapes project: {alias}")
            self.add("project/" + alias, path, item["sha256"])

        def include(alias, path):
            path = Path(path).resolve(strict=True)
            if path.is_dir():
                if output.is_relative_to(path):
                    raise ValueError("output must be outside material directories")
                for file in sorted(path.rglob("*")):
                    if file.is_file() and not file.is_symlink() and ".git" not in file.relative_to(path).parts:
                        resolved = file.resolve()
                        if resolved.is_relative_to(path):
                            self.add(alias + "/" + file.relative_to(path).as_posix(), resolved)
                return alias
            self.add(alias + "/" + path.name, path)
            return alias + "/" + path.name

        for library, record in stage1["libraries"].items():
            self.reference_paths[library] = [
                include(f"reference/{library}/{i}", path)
                for i, path in enumerate(record.get("materials", []))
            ]
        for i, path in enumerate(background):
            self.background.append(include(f"background/{i}", path))
        if contracts:
            file = Path(contracts).resolve(strict=True)
            loaded = json.loads(file.read_text(encoding="utf-8"))
            if not isinstance(loaded, dict):
                raise ValueError("reuse contracts must be indexed by stage-one function ID")
            for ident, record in loaded.items():
                node = stage1["graph"]["nodes"].get(ident)
                if not node or node["library"] == "target":
                    raise ValueError(f"reuse contract ID must name a reuse function: {ident}")
                if (not isinstance(record, dict) or not isinstance(record.get("path"), str)
                        or not all(type(record.get(key)) is int for key in ("start", "end"))):
                    raise ValueError(f"expected path, start and end for reuse contract {ident}")
                source = (file.parent / record["path"]).resolve(strict=True)
                if not source.is_file():
                    raise ValueError(f"reuse contract must be a file: {source}")
                alias = include("contracts/" + ident, source)
                self.contracts[ident] = {"path": alias, "start": record["start"], "end": record["end"]}
                self.reader().excerpt(**self.contracts[ident])
        self.sources = {library: Path(record["snapshot_root"]).relative_to("project").as_posix()
                        for library, record in stage1["libraries"].items()}
        for ident, node in stage1["graph"]["nodes"].items():
            if node["library"] == "target" and node["status"] == "definition":
                loc = node["source"]
                alias = self.alias("target", loc["path"])
                self.definitions.setdefault(alias, []).append({
                    "function_id": ident, "name": node["name"], "type": node["type"],
                    "line": loc["line"], "column": loc["column"],
                })
        self.compile_args = {}
        database = self.paths.get("project/compile_commands.json")
        if database:
            for command in json.loads(database.read_text(encoding="utf-8")):
                marker = "/project/"
                if marker in command["file"]:
                    relative = "project/" + command["file"].rsplit(marker, 1)[1]
                    self.compile_args[relative] = command["arguments"]

    def add(self, alias, path, expected=None):
        if not path.is_file():
            raise ValueError(f"material must be a regular file: {path}")
        digest = sha256(path)
        if expected and digest != expected:
            raise ValueError(f"stage-one snapshot file changed: {alias}")
        self.paths[alias] = path
        self.digests[alias] = digest

    def alias(self, library, path):
        return f"project/{self.sources[library]}/{path}"

    def reader(self):
        return SourceReader(self)

    def context_source(self, node, reader):
        loc = node["source"]
        path = self.alias(node["library"], loc["path"])
        return reader.excerpt(path, loc["line"], loc["end_line"])


class SourceReader(Reader):
    def __init__(self, materials):
        super().__init__(materials.root)
        self.materials = materials

    def path(self, name):
        if not isinstance(name, str) or name not in self.materials.paths:
            raise ValueError("use a file path from the run materials")
        return self.materials.paths[name]

    def canonical_name(self, name):
        return name

    def lines(self, name):
        lines, digest = super().lines(name)
        if digest != self.materials.digests[name]:
            raise ValueError(f"material changed during the run: {name}")
        return lines, digest

    def files(self, directory):
        if not isinstance(directory, str):
            raise ValueError("search path must be a string")
        prefix = "" if directory == "." else directory.rstrip("/") + "/"
        yield from (name for name in sorted(self.materials.paths) if name == directory or name.startswith(prefix))

    def execute(self, action):
        if action.get("tool") == "list":
            offset = self.integer(action, "offset", 0, 0, 1_000_000)
            files = list(self.files(action.get("path", ".")))
            return {"files": files[offset:offset + 100], "total": len(files), "next_offset": offset + 100}
        result = super().execute(action)
        if action.get("tool") == "read" and "start" in result:
            self.attach_definitions(result)
        return result

    def attach_definitions(self, result):
        definitions = [row for row in self.materials.definitions.get(result["path"], ())
                       if result["start"] <= row["line"] <= result["end"]]
        if definitions:
            result["definitions"] = definitions

    def excerpt(self, path, start, end):
        try:
            lines, digest = self.lines(path)
        except (OSError, ValueError) as exc:
            raise MaterialReadError(f"cannot read required source {path}: {exc}") from exc
        if not 1 <= start <= end <= len(lines):
            raise MaterialReadError(f"invalid source interval: {path}:{start}-{end}")
        text = "\n".join(lines[start - 1:end])
        self.reads.setdefault(path, []).append((start, end, digest))
        result = {"path": path, "start": start, "end": end, "text": text}
        self.attach_definitions(result)
        return result

    def check_citation(self, citation):
        if not isinstance(citation, dict) or set(citation) != {"path", "start", "end"}:
            raise ValueError("citations must contain path, start and end")
        path, start, end = citation["path"], citation["start"], citation["end"]
        intervals = self.reads.get(path, []) if isinstance(path, str) else []
        if type(start) is not int or type(end) is not int or not 1 <= start <= end:
            raise ValueError(f"invalid citation: {citation}")
        last = start - 1
        for first, final, _ in sorted(intervals):
            if first <= last + 1:
                last = max(last, final)
            if last >= end:
                return
        raise ValueError(f"source interval was not delivered: {citation}")
