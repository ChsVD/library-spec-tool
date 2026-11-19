"""Read the Stage 2 handoff and locate source evidence within its bound inputs."""

from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path

from stage1.inputs import sha256 as file_sha256
from stage2.materials import MaterialReadError
from stage2.reader import Reader
from stage2.schedule import digest


class EvidenceUnavailable(MaterialReadError):
    """A pinned source is absent, unreadable, or has changed."""


def load_evidence(stage2_result, *, stage1_result=None, top_level_spec=None, background=()):
    """Load Stage 2 and verify the Stage 1 result against its recorded digest."""
    stage2_path = Path(stage2_result).resolve(strict=True)
    stage2_bytes = stage2_path.read_bytes()
    stage2 = json.loads(stage2_bytes)
    if stage2.get("schema_version") != 1:
        raise ValueError("expected a stage-two result with schema_version 1")
    stage1_path = Path(stage1_result) if stage1_result is not None else stage2_path.parent / stage2["stage1_result"]
    stage1_path = stage1_path.resolve(strict=True)
    stage1_bytes = stage1_path.read_bytes()
    stage1_hash = sha256(stage1_bytes).hexdigest()
    if stage1_hash != stage2["identity"]["stage1_sha256"]:
        raise ValueError("stage-one result does not match the stage-two handoff SHA-256")
    stage1 = json.loads(stage1_bytes)
    if stage1.get("schema_version") != 1 or stage1.get("status") not in ("analysis_completed", "partial_analysis"):
        raise ValueError("expected a completed or partial stage-one result with schema_version 1")
    return Evidence(
        stage1_path.parent, stage1, stage2, stage1_hash, sha256(stage2_bytes).hexdigest(),
        top_level_spec, background,
    )


def _relative_path(value):
    path = Path(value)
    if not path.parts or path.is_absolute() or ".." in path.parts or '\\' in value:
        raise ValueError(f"expected a relative material path: {value}")
    return path


class Evidence:
    def __init__(self, stage1_root, stage1, stage2, stage1_hash, stage2_hash, top_level_spec, background):
        self.stage1 = stage1
        self.stage2 = stage2
        self.nodes = stage1["graph"]["nodes"]
        self.libraries = stage1["libraries"]
        self.project = stage1_root / "project"
        self.contract_intervals = stage2["identity"].get("reuse_contracts", {})
        self.source_catalog = {}
        self._materials = {}
        self._source_ids = {}
        self._top_level = []
        self._supplemental = []
        for record in stage1["provenance"]["snapshot_files"]:
            relative = _relative_path(record["path"])
            alias = (Path("project") / relative).as_posix()
            kind = "compile_commands" if alias == "project/compile_commands.json" else "project_source"
            self._register(alias, self.project / relative, record["sha256"], kind)
        for alias, record in stage2.get("external_materials", {}).items():
            if alias.startswith("project/"):
                raise ValueError(f"external material shadows a stage-one snapshot path: {alias}")
            prefix = _relative_path(alias).parts[0]
            kind = {"background": "background", "contracts": "reuse_contract"}.get(prefix, "stage2_evidence")
            path = stage1_root / record["path"]
            self._register(alias, path, record["sha256"], kind)
        if top_level_spec is not None:
            self._top_level.append(self._add_input("top_level", 0, top_level_spec))
        for number, path in enumerate(background):
            path = Path(path).resolve(strict=True)
            if path.is_dir():
                for relative in Reader(path).files("."):
                    file = path / relative
                    if not file.is_symlink() and ".git" not in Path(relative).parts:
                        self._add_input("background", number, file, relative=relative)
            else:
                self._supplemental.append(self._add_input("background", number, path))
        self.identity = {
            "stage1_sha256": stage1_hash,
            "stage2_sha256": stage2_hash,
            "stage2_materials_sha256": stage2["identity"].get("materials_sha256"),
            "evidence_sha256": digest({
                "materials": self.source_catalog,
                "top_level": self._top_level,
                "supplemental": self._supplemental,
            }),
        }
        self.needs, self.blocked_functions = self._build_needs()

    def _register(self, alias, path, expected, kind):
        if alias in self._materials:
            raise ValueError(f"duplicate material path: {alias}")
        file_id = "file-" + digest([alias, expected])[:24]
        self._materials[alias] = Path(path)
        self._source_ids[alias] = file_id
        self.source_catalog[file_id] = {"id": file_id, "path": alias, "file_sha256": expected, "kind": kind}

    def _add_input(self, role, number, supplied, *, relative=None):
        path = Path(supplied).resolve(strict=True)
        if not path.is_file():
            raise ValueError(f"expected a supplemental material file: {path}")
        alias = f"supplemental/{role}/{number}/{relative or path.name}"
        self._register(alias, path, file_sha256(path), role)
        return alias

    def _build_needs(self):
        functions = self.stage2["functions"]
        sites = self.stage2["calls"]
        checks, requirements, call_by_function = defaultdict(list), {}, defaultdict(dict)
        for owner, function in functions.items():
            if owner not in self.nodes:
                raise ValueError(f"stage-two function has no bound stage-one identity: {owner}")
            for call_id, check in function.get("call_checks", {}).items():
                if call_id not in sites:
                    raise ValueError(f"stage-two check names an unknown call ID: {call_id}")
                if check.get("call_id", call_id) != call_id:
                    raise ValueError(f"stage-two check disagrees with its call ID: {call_id}")
                checks[call_id].append({"saved_by": owner, "check": check})
            for requirement in (function.get("draft") or {}).get("call_requirements", []):
                call_id = requirement["call_id"]
                if call_id not in sites or sites[call_id]["caller"] != owner:
                    raise ValueError(f"stage-two call requirement has no matching caller: {call_id}")
                if call_id in requirements:
                    raise ValueError(f"duplicate stage-two call requirement: {call_id}")
                requirements[call_id] = requirement
        for call_id, site in sites.items():
            caller, callee = site["caller"], site.get("callee")
            if caller not in self.nodes or (callee is not None and callee not in self.nodes):
                raise ValueError(f"stage-two call has no bound stage-one identity: {call_id}")
            row = {"call_id": call_id, "site": site, "requirement": requirements.get(call_id),
                   "checks": checks[call_id]}
            call_by_function[caller][call_id] = row
            if callee is not None:
                call_by_function[callee][call_id] = row

        needs, blocked = {}, []
        for function_id, function in functions.items():
            draft = function.get("draft")
            status = {"status": function["status"], "reason": function.get("reason"),
                      "unverified_dependencies": function.get("unverified_dependencies", [])}
            calls = list(call_by_function[function_id].values())
            conflicts = [
                call["call_id"] for call in calls
                if any(row["check"]["status"] == "conflict" for row in call["checks"])
            ]
            if draft is None:
                blocked.append({"function_id": function_id, "function": self.nodes[function_id], **status,
                                "calls": calls, "conflicting_call_ids": conflicts})
                continue
            for number, original in enumerate(draft["common_needs"], 1):
                need_id = f"{function_id}:{number}:{digest(original)[:16]}"
                needs[need_id] = {
                    "id": need_id, "function_id": function_id, "ordinal": number, "original": original,
                    **status, "calls": calls, "conflicting_call_ids": conflicts,
                    "formal_call_validation": self.stage2.get("formal_call_validation", "not_run"),
                }
        for function_id in self.stage2.get("scope", {}).get("function_ids", []):
            if function_id not in functions:
                blocked.append({"function_id": function_id, "function": self.nodes[function_id],
                                "status": "pending", "reason": "stage-two draft has not been produced",
                                "calls": list(call_by_function[function_id].values())})
        return needs, blocked

    def _lines(self, alias):
        if alias not in self._materials:
            raise MaterialReadError(f"material path is absent from the bound inputs: {alias}")
        material = self._materials[alias]
        expected = self.source_catalog[self._source_ids[alias]]["file_sha256"]
        try:
            if alias.startswith("project/"):
                base = self.project
                relative = material.relative_to(base)
                if base.is_symlink():
                    raise ValueError("stage-one project root must stay within its run directory")
            else:
                base, relative = material.parent, Path(material.name)
            lines, actual = Reader(base).lines(relative.as_posix())
        except OSError as exc:
            raise EvidenceUnavailable(f"cannot read {alias}: {exc}") from exc
        except ValueError as exc:
            raise MaterialReadError(f"cannot read {alias}: {exc}") from exc
        if actual != expected:
            raise EvidenceUnavailable(f"SHA-256 changed for {alias}: expected {expected}, found {actual}")
        return lines

    def verify_files(self, expected_by_path):
        """Revalidate each pinned file once before reusing durable evidence."""
        for path, expected in expected_by_path.items():
            file_id = self._source_ids.get(path)
            if file_id is None or self.source_catalog[file_id]["file_sha256"] != expected:
                raise MaterialReadError(f"pinned evidence identity differs for {path}")
            self._lines(path)

    def _excerpt(self, alias, start, end, lines, **metadata):
        if type(start) is not int or type(end) is not int or not 1 <= start <= end <= len(lines):
            raise MaterialReadError(f"invalid source interval for {alias}: {start}-{end}")
        text = "\n".join(lines[start - 1:end])
        if len(text) > 24000:
            raise MaterialReadError(f"source interval exceeds 24000 characters: {alias}:{start}-{end}")
        file_id = self._source_ids[alias]
        return {**self.source_catalog[file_id], **metadata, "file_id": file_id,
                "id": "source-" + digest([file_id, start, end])[:24],
                "start_line": start, "end_line": end, "text": text}

    def read_source(self, source_id, start_line=None, end_line=None):
        """Read an interval in one cataloged evidence file and verify its pinned content."""
        entry = self.source_catalog.get(source_id)
        if entry is None:
            raise MaterialReadError(f"unknown evidence file ID: {source_id}")
        alias = entry["path"]
        lines = self._lines(alias)
        start = 1 if start_line is None else start_line
        end = len(lines) if end_line is None else end_line
        return self._excerpt(alias, start, end, lines)

    def _alias(self, node, path):
        root = _relative_path(self.libraries[node["library"]]["snapshot_root"])
        if not root.is_relative_to("project"):
            raise ValueError("library snapshot root is outside the stage-one project")
        return (root / _relative_path(path)).as_posix()

    def _reuse_contract(self, callee, index, read, add, read_errors):
        from .index_formats import parse_c

        node = self.nodes[callee]
        library_id, relative = node["library"], node["source"]["path"]
        library = self.libraries[library_id]
        symbol = node["symbol"]
        source = self._alias(node, relative)
        explicit = self.contract_intervals.get(callee)
        source_ids = []
        explicit_entry = None
        if explicit:
            explicit_entry = add(explicit["path"], explicit["start"], explicit["end"],
                                 kind="reuse_contract_interval", function_id=callee)
            if explicit_entry:
                source_ids.append(explicit_entry["id"])
        # Parse C annotations from same-identity source or a callee-bound Stage 2 interval.
        # Read complete files for parsing, and deliver only the matched declarations.
        matches = {}
        for alias in dict.fromkeys([source, *([explicit["path"]] if explicit else [])]):
            lines = read(alias)
            if lines is None or Path(alias).suffix.lower() not in (".c", ".h"):
                continue
            raw = "\n".join(lines)
            try:
                parsed, _ = parse_c(raw)
            except ValueError as exc:
                read_errors.append({"path": alias, "status": "parse_failed", "error": str(exc),
                                    "retryable": False})
                continue
            actual = self.source_catalog[self._source_ids[alias]]["file_sha256"]
            for row in parsed:
                if row["kind"] != "contract" or row["name"] not in (symbol, node["name"]):
                    continue
                start = raw.count("\n", 0, row["start"]) + 1
                end = raw.count("\n", 0, row["end"] - 1) + 1
                same_explicit_file = explicit_entry and explicit_entry["file_sha256"] == actual
                if same_explicit_file and not explicit["start"] <= start <= end <= explicit["end"]:
                    continue
                key = actual, start, end
                if key not in matches:
                    entry = add(alias, start, end, kind="reuse_contract_branch",
                                function_id=callee, structure=row["structure"])
                    if entry:
                        matches[key] = entry
        candidates = {}
        if index is not None:
            source_paths = [relative, str(Path(library["source_root"]) / relative)]
            if explicit and explicit_entry is not None:
                source_paths.append(str(self._materials[explicit["path"]]))
            expected = self.source_catalog.get(self._source_ids.get(source), {}).get("file_sha256")
            for path in dict.fromkeys(source_paths):
                for row in index.find_contracts(symbol, library_id, path, role="reuse"):
                    same_explicit_file = explicit_entry and explicit_entry["file_sha256"] == row["file_sha256"]
                    if same_explicit_file and not explicit["start"] <= row["start_line"] <= row["end_line"] <= explicit["end"]:
                        continue
                    binding = ("source_digest_match" if same_explicit_file or row["file_sha256"] == expected
                               else "same_library_path_unverified")
                    candidates[row["id"]] = {**row, "binding": binding}
        return {"function": node, "version": library.get("version"), "binding": explicit,
                "source_ids": source_ids + [row["id"] for row in matches.values()],
                "branches": [{key: value for key, value in row.items() if key != "text"}
                             for row in matches.values()],
                "candidates": list(candidates.values()),
                "status": "located" if source_ids or matches or candidates else "unavailable"}

    def for_need(self, need_id, index=None):
        """Deliver original evidence and separately report each unavailable location."""
        need = self.needs[need_id]
        function_id = need["function_id"]
        node = self.nodes[function_id]
        draft = self.stage2["functions"][function_id]["draft"]
        delivered, lines_by_alias, read_errors = {}, {}, []

        def read(alias, start=None, end=None):
            try:
                if alias not in lines_by_alias:
                    lines_by_alias[alias] = self._lines(alias)
                return lines_by_alias[alias]
            except MaterialReadError as exc:
                failure = {"path": alias, "start_line": start, "end_line": end, "error": str(exc),
                           "status": "read_failed", "retryable": isinstance(exc, EvidenceUnavailable)}
                if failure not in read_errors:
                    read_errors.append(failure)
                return None

        def add(alias, start, end, **metadata):
            lines = read(alias, start, end)
            if lines is None:
                return None
            try:
                entry = self._excerpt(alias, start, end, lines, **metadata)
            except MaterialReadError as exc:
                failure = {"path": alias, "start_line": start, "end_line": end, "error": str(exc),
                           "status": "invalid_interval", "retryable": False}
                if failure not in read_errors:
                    read_errors.append(failure)
                return None
            return delivered.setdefault(entry["id"], entry)

        location = node["source"]
        add(self._alias(node, location["path"]), location["line"], location["end_line"], kind="function_source")
        for citation in [*need["original"].get("evidence", []), *draft.get("evidence", [])]:
            add(citation["path"], citation["start"], citation["end"])
        for alias in [*self._top_level, *self._supplemental]:
            lines = read(alias)
            if lines:
                size = 0
                for end, line in enumerate(lines[:200], 1):
                    size += len(line) + 1
                    if size > 24000:
                        end = max(1, end - 1)
                        break
                add(alias, 1, end)

        calls = []
        reuse_contracts = {}
        related_functions = {}
        for call in need["calls"]:
            site, call_loc = call["site"], call["site"]["location"]
            path, line = call_loc.get("path"), call_loc.get("line")
            call_evidence = None
            if path and type(line) is int and line > 0:
                call_evidence = add(path, line, line, kind="call_source")
            calls.append({**call, "source_id": call_evidence["id"] if call_evidence else None})
            caller, callee = site["caller"], site.get("callee")
            if callee and site["kind"] == "reuse" and callee not in reuse_contracts:
                reuse_contracts[callee] = self._reuse_contract(callee, index, read, add, read_errors)
            for other in (caller, callee):
                related = self.stage2["functions"].get(other)
                if related is not None and other != function_id and other not in related_functions:
                    related_functions[other] = {
                        "function": self.nodes[other],
                        **{key: related.get(key) for key in ("status", "reason", "unverified_dependencies")},
                        "cases": (related.get("draft") or {}).get("cases", []),
                        "assumptions": (related.get("draft") or {}).get("assumptions", []),
                    }

        compile_args = {}
        database_alias = "project/compile_commands.json"
        if database_alias in self._materials:
            lines = read(database_alias)
            if lines is not None:
                try:
                    units = {self._alias(unit, unit["path"]) for unit in node.get("translation_units", [])}
                    for row in json.loads("\n".join(lines)):
                        file_name = row["file"]
                        if "/project/" in file_name:
                            alias = "project/" + file_name.rsplit("/project/", 1)[1]
                            if alias in units:
                                compile_args[alias] = row["arguments"]
                except (ValueError, TypeError, KeyError) as exc:
                    read_errors.append({"path": database_alias, "status": "parse_failed", "error": str(exc),
                                        "retryable": False})

        return {
            "function": node, "draft": {k: v for k, v in draft.items() if k not in ("common_needs", "call_requirements")},
            "configuration": self.stage1["configuration"], "compile_arguments": compile_args,
            "compile_commands": self.source_catalog.get(self._source_ids.get(database_alias)),
            "calls": calls, "related_functions": related_functions, "reuse_contracts": reuse_contracts,
            "sources": list(delivered.values()), "read_errors": read_errors,
            "analysis_gaps": [row for row in self.stage2.get("analysis_gaps", []) if row["caller"] == function_id],
            "analysis_translation_failures": self.stage2.get("analysis_translation_failures", []),
        }
