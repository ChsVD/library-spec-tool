"""Read-only, format-aware index of the reference libraries supplied to stage three."""

from bisect import bisect_right
from collections import defaultdict
from copy import deepcopy
from fnmatch import fnmatchcase
from hashlib import sha256
import json
from math import log
from pathlib import Path, PurePosixPath
import re

from .index_formats import ROC_GENERATED_FILE, ROC_WITNESS, SYMBOLS, parse_c, parse_rocq, parse_strategies


INDEX_VERSION = 1
MAX_FILE_BYTES = 8_000_000
PARSERS = {".c": parse_c, ".h": parse_c, ".v": parse_rocq,
           ".strategies": parse_strategies}
WORDS = re.compile(r"[^\W_]+", re.UNICODE)
CAMEL = re.compile(r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])")
STOP = set("a an and are as at be by can for from has in into is it may of on or that the "
           "their this to was what when where which will with".split())
KIND_ALIASES = {
    "definition": ("Definition", "Fixpoint", "CoFixpoint", "Inductive", "Record",
                   "Variant", "CoInductive", "Class", "Instance", "Let"),
    "lemma": ("Lemma", "Theorem", "Remark", "Fact", "Proposition", "Corollary", "Example"),
}


def stable_id(prefix, *parts):
    data = json.dumps(parts, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return prefix + "_" + sha256(data.encode()).hexdigest()[:24]


def normalize_symbol(symbol):
    return symbol.replace("::", ".")


def source_words(text):
    return {normalize_symbol(match[0]) for match in SYMBOLS.finditer(text)}


def terms(text):
    result = set()
    for match in WORDS.finditer(text):
        value = match[0]
        result.add(value.casefold())
        result.update(piece.casefold() for piece in CAMEL.split(value))
    # Singular/plural normalization helps ordinary queries without domain dictionaries.
    return {word[:-1] if len(word) > 4 and word.endswith("s") and not word.endswith("ss") else word
            for word in result if len(word) > 1 and word not in STOP}


def safe_path(root, relative):
    candidate = (root / relative).resolve(strict=True)
    if not candidate.is_relative_to(root):
        raise ValueError(f"Reference path escapes its library root: {relative}")
    if not candidate.is_file():
        raise ValueError(f"Reference path is not a regular file: {relative}")
    return candidate


def read_source(root, relative):
    path = safe_path(root, relative)
    if path.stat().st_size > MAX_FILE_BYTES:
        raise ValueError(f"Reference file exceeds the {MAX_FILE_BYTES}-byte limit: {relative}")
    data = path.read_bytes()
    if b"\0" in data:
        raise ValueError(f"Binary reference file: {relative}")
    return data.decode("utf-8"), sha256(data).hexdigest()


def input_libraries(manifest):
    base = Path.cwd()
    if isinstance(manifest, (str, Path)):
        manifest_path = Path(manifest).resolve(strict=True)
        base = manifest_path.parent
        manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
    if isinstance(manifest, dict):
        manifest = manifest["libraries"]
    if not isinstance(manifest, (list, tuple)):
        raise ValueError("Reference manifest requires a libraries list")
    seen = set()
    for item in manifest:
        if not isinstance(item, dict):
            raise ValueError("Each reference library must be an object")
        name = item.get("id")
        role = item.get("role", "reference")
        root_name = item.get("root")
        if not isinstance(name, str) or not name.strip() or name in seen:
            raise ValueError("Reference library IDs must be unique nonempty strings")
        if role not in {"reference", "reuse"}:
            raise ValueError(f"Unsupported reference library role for {name}: {role}")
        if not isinstance(root_name, (str, Path)):
            raise ValueError(f"Reference library requires a root: {name}")
        root = (base / root_name).resolve(strict=True)
        patterns = item.get("files")
        if root.is_file() and patterns is None:
            root, patterns = root.parent, [root.name]
        if not root.is_dir():
            raise ValueError(f"Invalid reference library root: {name}")
        if patterns is not None and (not isinstance(patterns, list) or any(
                not isinstance(pattern, str) or not pattern or PurePosixPath(pattern).is_absolute()
                or ".." in PurePosixPath(pattern).parts or "\\" in pattern for pattern in patterns)):
            raise ValueError(f"Reference file patterns must be library-relative POSIX paths: {name}")
        seen.add(name)
        yield name, root, role, patterns, deepcopy(item.get("configuration")), deepcopy(item.get("version"))


def library_files(root, patterns):
    if patterns is None:
        # Keep explicit unsupported paths visible without ingesting every artifact in a library root.
        for path in sorted(root.rglob("*")):
            if path.suffix.lower() in PARSERS and path.is_file():
                yield path.relative_to(root).as_posix()
        return
    files = set()
    for pattern in patterns:
        if not any(ch in pattern for ch in "*?["):
            files.add(PurePosixPath(pattern).as_posix())
            continue
        matches = {p.relative_to(root).as_posix() for p in root.glob(pattern) if p.is_file()}
        if not matches:
            raise ValueError(f"Reference file pattern has no matches: {pattern}")
        files.update(matches)
    yield from sorted(files)


def page(values, key, limit, offset):
    if type(limit) is not int or not 1 <= limit <= 100:
        raise ValueError("limit must be an integer from 1 to 100")
    if type(offset) is not int or offset < 0:
        raise ValueError("offset must be a nonnegative integer")
    end = offset + limit
    return {key: values[offset:end], "total": len(values), "offset": offset,
            "next_offset": end if end < len(values) else None, "truncated": end < len(values)}


def strings(value, name):
    if isinstance(value, str):
        return [value]
    if isinstance(value, (list, tuple)) and all(isinstance(word, str) for word in value):
        return value
    raise ValueError(f"{name} must be a string or list of strings")


class ReferenceIndex:
    """Static postings and source coordinates for a fixed reference snapshot."""

    def __init__(self, manifest):
        self._files = {}
        self._entries = {}
        self._entries_by_file = defaultdict(list)
        self._entry_terms = defaultdict(set)
        self._file_terms = defaultdict(set)
        self._symbols = defaultdict(set)
        self._mentions = defaultdict(set)
        self._entry_symbols = {}
        self._module_files = defaultdict(set)
        self._roots = {}
        libraries = []
        for library, root, role, patterns, configuration, version in sorted(input_libraries(manifest)):
            self._roots[library] = root
            library_files_identity = []
            for relative in library_files(root, patterns):
                file = self._add_file(library, relative, role, configuration, version)
                library_files_identity.append({key: file[key] for key in ("path", "file_sha256", "status")})
            libraries.append({"id": library, "root": str(root), "role": role, "version": version,
                              "configuration": configuration, "files": library_files_identity})
        self.identity = {"index_version": INDEX_VERSION, "libraries": libraries,
                         "digest": stable_id("index", INDEX_VERSION, libraries)}

    def _add_file(self, library, relative, role, configuration, version):
        file_id = stable_id("file", library, relative)
        suffix = PurePosixPath(relative).suffix.lower()
        file = {"id": file_id, "library_id": library, "role": role, "path": relative,
                "format": suffix, "version": version, "configuration": configuration,
                "status": "indexed" if suffix in PARSERS else "text_only", "links": [],
                "file_sha256": None, "entry_count": 0}
        self._files[file_id] = file
        try:
            raw, digest = read_source(self._roots[library], relative)
        except (ValueError, OSError, UnicodeError) as exc:
            file.update(status="unreadable", error=str(exc))
            raw = ""
        else:
            file["file_sha256"] = digest
        if suffix == ".v":
            self._module_files[PurePosixPath(relative).stem].add(file_id)
        for term in terms(f"{relative}\n{raw}"):
            self._file_terms[term].add(file_id)
        if not raw:
            return file
        scanned, file["links"] = PARSERS[suffix](raw) if suffix in PARSERS else ([], [])
        newlines = [match.start() for match in re.finditer(r"\n", raw)]

        def line(offset):
            return bisect_right(newlines, offset - 1) + 1

        for item in sorted(scanned, key=lambda e: (e["start"], e["end"], e["kind"])):
            identifier = stable_id("entry", file_id, digest, item["start"], item["end"], item["kind"])
            item.update(id=identifier, file_id=file_id, library_id=library, path=relative,
                        role=role, file_sha256=digest, version=version, configuration=configuration,
                        start_line=line(item["start"]), end_line=line(item["end"] - 1),
                        start_column=item["start"] - (newlines[line(item["start"]) - 2] + 1
                                     if line(item["start"]) > 1 else 0) + 1)
            if "evidence_start" in item:
                item.update(evidence_start_line=line(item["evidence_start"]),
                            evidence_end_line=line(item["evidence_end"] - 1))
            item.setdefault("qualified_name", item["name"])
            source = raw[item["start"]:item["end"]]
            item["_snippet"] = " ".join(source.split())[:220]
            item["_name_terms"] = terms(item["qualified_name"])
            matched_terms = terms(f"{item['qualified_name']}\n{source}")
            item["_term_count"] = len(matched_terms)
            shape = item["structure"]
            if item["kind"] == "rocq_declaration":
                forms = shape.get("generated_forms", [])
                if "FuncSig" in forms:
                    shape["generated_role"] = "function_signature"
                elif "Spec" in forms or "HoareFun" in forms:
                    shape["generated_role"] = "function_specification"
                elif ROC_GENERATED_FILE.search(relative) or ROC_WITNESS.search(item["name"]):
                    shape["generated_role"] = "verification_material"
            by_name = normalize_symbol(item["qualified_name"])
            self._symbols[by_name].add(identifier)
            self._symbols[by_name.rsplit(".", 1)[-1]].add(identifier)
            if item["kind"] == "rocq_declaration":
                module = PurePosixPath(relative).with_suffix("")
                for start in range(len(module.parts)):
                    qualified = ".".join((*module.parts[start:], by_name))
                    self._symbols[qualified].add(identifier)
            self._entries[identifier] = item
            self._entries_by_file[file_id].append(identifier)
            for term in matched_terms:
                self._entry_terms[term].add(identifier)
            symbols = source_words(source)
            reference_text = item.pop("reference_text", None)
            self._entry_symbols[identifier] = source_words(reference_text) if reference_text is not None else symbols
            for symbol in symbols:
                self._mentions[symbol].add(identifier)
                if "." in symbol:
                    self._mentions[symbol.rsplit(".", 1)[-1]].add(identifier)
        file["entry_count"] = len(scanned)
        return file

    def _scope(self, ids):
        files = [self._files[file_id] for file_id in sorted(ids)]
        return {"index_digest": self.identity["digest"], "file_count": len(files),
                "library_ids": sorted({file["library_id"] for file in files}),
                "unreadable_files": sum(file["status"] == "unreadable" for file in files)}

    def _file(self, identifier):
        if identifier not in self._files:
            raise ValueError(f"Unknown reference file ID: {identifier}")
        return self._files[identifier]

    def _entry(self, identifier):
        if identifier not in self._entries:
            raise ValueError(f"Unknown reference entry ID: {identifier}")
        return self._entries[identifier]

    @staticmethod
    def _file_card(item):
        return deepcopy({k: v for k, v in item.items() if k != "links"})

    def entry_card(self, entry_id):
        entry = self._entry(entry_id)
        card = {key: entry[key] for key in ("id", "file_id", "library_id", "role", "path",
                                            "file_sha256", "version", "configuration", "start_line",
                                            "end_line", "start_column", "name", "qualified_name", "kind")}
        for key in ("declaration_kind", "scope", "evidence_start_line", "evidence_end_line"):
            if key in entry:
                card[key] = entry[key]
        card["snippet"] = entry["_snippet"]
        structure = entry["structure"]
        card["structure"] = {key: structure[key] for key in (
            "status", "branch", "proof_ending", "operator", "rule_number", "generated_forms",
            "generated_function_context", "generated_role") if key in structure}
        if "operations" in structure:
            card["structure"]["actions"] = sorted({op.get("side", "unknown") + "_" + op["operation"]
                                                   for op in structure["operations"]})
        return deepcopy(card)

    def _text(self, file):
        try:
            raw, digest = read_source(self._roots[file["library_id"]], file["path"])
        except (ValueError, OSError, UnicodeError) as exc:
            raise OSError(f"Cannot read {file['library_id']}:{file['path']}: {exc}") from exc
        if digest != file["file_sha256"]:
            raise OSError(f"Reference changed after indexing: {file['library_id']}:{file['path']}")
        return raw

    def read_entry(self, entry_id):
        item = self._entry(entry_id)
        file = self._files[item["file_id"]]
        raw = self._text(file)
        result = self.entry_card(entry_id)
        result.update(text=raw[item["start"]:item["end"]], structure=deepcopy(item["structure"]),
                      file_links=deepcopy(file["links"]))
        if "links" in item:
            result["links"] = deepcopy(item["links"])
        if "evidence_start" in item:
            result["contract_text"] = raw[item["evidence_start"]:item["evidence_end"]]
        return result

    def _rank_files(self, query, ids):
        needles = terms(query)
        scores = defaultdict(float)
        matching = defaultdict(set)
        for term in needles:
            posting = self._file_terms[term]
            weight = log(1 + len(self._files) / max(1, len(posting)))
            for identifier in ids.intersection(posting):
                scores[identifier] += weight
                matching[identifier].add(term)
        # Full relative path queries remain usable when terms are otherwise shared.
        literal = query.casefold().strip()
        for identifier in ids:
            path = self._files[identifier]["path"]
            if literal and literal in path.casefold():
                scores[identifier] += 4
        return [(identifier, scores[identifier], sorted(matching[identifier]))
                for identifier in sorted(scores, key=lambda i: (-scores[i], self._order(self._files[i])))]

    @staticmethod
    def _order(item):
        return item["library_id"], item["path"], item.get("start_line", 0), item.get("id", "")

    def _fragment(self, file, matching):
        if not matching or file["status"] == "unreadable":
            return None
        try:
            raw = self._text(file)
        except OSError as exc:
            return {"error": str(exc), "retryable": True}
        needles = set(matching)
        best = None
        for number, line in enumerate(raw.split("\n"), 1):
            common = len(terms(line).intersection(needles))
            if common and (best is None or common > best[0]):
                best = (common, number, line.strip()[:220])
                if common == len(needles):
                    break
        return {"line": best[1], "snippet": best[2]} if best else None

    def list_files(self, query="", limit=20, offset=0):
        if not isinstance(query, str):
            raise ValueError("File query must be a string")
        ids = set(self._files)
        if query.strip():
            ranked = self._rank_files(query, ids)
        else:
            ranked = [(fid, 0, []) for fid in sorted(ids, key=lambda i: self._order(self._files[i]))]
        result = page(ranked, "files", limit, offset)
        result["files"] = [{**self._file_card(self._files[fid]), "score": round(score, 3),
                            "matched_terms": matching, "fragment": self._fragment(self._files[fid], matching)}
                           for fid, score, matching in result["files"]]
        return {**result, "scope": self._scope(ids)}

    def list_entries(self, file_id, limit=20, offset=0, query=""):
        self._file(file_id)
        if query:
            result = self.search_references({"text": query, "file_id": file_id, "limit": limit,
                                             "offset": offset})
            result["entries"] = result.pop("hits")
            return result
        result = page(self._entries_by_file[file_id], "entries", limit, offset)
        result["entries"] = [self.entry_card(identifier) for identifier in result["entries"]]
        return {**result, "scope": self._scope({file_id})}

    def _rank_entries(self, query, ids):
        generic = terms(" ".join(strings(query.get("text", ""), "text")) + " " +
                        " ".join(strings(query.get("objects", ""), "objects")))
        have = terms(" ".join(strings(query.get("have", ""), "have")))
        need = terms(" ".join(strings(query.get("need", ""), "need")))
        symbols = {normalize_symbol(s) for s in strings(query.get("symbols", []), "symbols") if s}
        scores = defaultdict(float)
        matches = defaultdict(set)
        directional = {}
        for term in generic | have | need:
            posting = self._entry_terms[term]
            weight = log(1 + len(self._entries) / max(1, len(posting)))
            for identifier in posting:
                entry = self._entries[identifier]
                if entry["file_id"] in ids:
                    if term in entry["_name_terms"]:
                        scores[identifier] += 1.7 * weight
                    else:
                        length = 1 + 0.25 * log(1 + entry["_term_count"] / 24)
                        scores[identifier] += weight / length
                    matches[identifier].add(term)
        symbol_matches = defaultdict(set)
        for symbol in symbols:
            declarations = self._symbols[symbol]
            for identifier in declarations | self._mentions[symbol]:
                if self._entries[identifier]["file_id"] in ids:
                    scores[identifier] += 12 if identifier in declarations else 6
                    symbol_matches[identifier].add(symbol)
        kinds = {kind.casefold() for kind in strings(query.get("kind", []), "kind") if kind}
        kinds |= {alias.casefold() for kind in kinds for alias in KIND_ALIASES.get(kind, ())}
        if kinds and not (generic or have or need or symbols):
            scores.update({i: 0 for fid in ids for i in self._entries_by_file[fid]})
        for identifier in list(scores):
            entry = self._entries[identifier]
            shape = entry["structure"]
            entry_kinds = {entry["kind"], entry.get("declaration_kind", "").casefold()}
            if "generated_role" in shape:
                entry_kinds.update(("verification", shape["generated_role"]))
            if kinds and not kinds.intersection(entry_kinds):
                del scores[identifier]
                continue
            if "definition" in kinds and shape.get("generated_role") and not symbol_matches[identifier]:
                scores[identifier] *= 0.65
            if have or need:
                before, after = self._direction(entry)
                direct = (have & before, need & after)
                reverse = (have & after, need & before)
                directional[identifier] = {"have": sorted(direct[0]), "need": sorted(direct[1]),
                                           "reverse_have": sorted(reverse[0]),
                                           "reverse_need": sorted(reverse[1])}
                scores[identifier] += 4 * sum(map(len, direct)) - 2 * sum(map(len, reverse))
        return sorted(scores, key=lambda i: (-scores[i], self._order(self._entries[i]))), scores, matches, symbol_matches, directional

    @staticmethod
    def _direction(entry):
        structure = entry["structure"]
        if entry["kind"] == "strategy":
            operations = structure["operations"]
            before = " ".join(structure["left"] + structure["check"])
            after = " ".join([*structure["right"], *(op["argument"] for op in operations
                             if op.get("side") == "left" and op["operation"] == "add")])
        elif entry["kind"] == "contract":
            before, after = structure.get("require") or "", structure.get("ensure") or ""
        elif structure.get("operator") in {"<->", "↔", "⊣⊢"}:
            before = after = " ".join([structure.get("left", ""), structure.get("right", "")])
        else:
            before = " ".join([*structure.get("premises", []), structure.get("left", "")])
            after = structure.get("conclusion", "")
        return terms(before), terms(after)

    def search_references(self, query):
        if isinstance(query, str):
            query = {"text": query}
        if not isinstance(query, dict):
            raise ValueError("Reference query must be an object or string")
        file_id = query.get("file_id")
        if file_id is not None:
            self._file(file_id)
        library = query.get("library_id")
        role = query.get("role")
        ids = {i for i, file in self._files.items()
               if (file_id is None or i == file_id) and (library is None or library == file["library_id"])
               and (role is None or role == file["role"])}
        ranked, scores, matches, symbols, directions = self._rank_entries(query, ids)
        result = page(ranked, "hits", query.get("limit", 20), query.get("offset", 0))
        result["hits"] = [{**self.entry_card(i), "score": round(scores[i], 3),
                           "matched_terms": sorted(matches[i]), "matched_symbols": sorted(symbols[i]),
                           "direction_match": directions.get(i)} for i in result["hits"]]
        file_query = " ".join(word for key in ("text", "objects", "have", "need", "symbols")
                              for word in strings(query.get(key, ""), key))
        result["files"] = [
            {**self._file_card(self._files[i]), "score": round(score, 3), "matched_terms": hits,
             "fragment": self._fragment(self._files[i], hits)}
            for i, score, hits in self._rank_files(file_query, ids)[:min(query.get("limit", 20), 10)]
        ]
        return {**result, "scope": self._scope(ids)}

    def find_contracts(self, symbol, library_id=None, path=None, *, role=None):
        found = []
        for identifier in self._symbols.get(symbol, ()):
            item = self._entries[identifier]
            if item["kind"] != "contract" or item["name"] != symbol:
                continue
            if library_id is not None and library_id != item["library_id"]:
                continue
            if role is not None and role != item["role"]:
                continue
            if path is not None:
                source = Path(path)
                if source.is_absolute():
                    root = self._roots[item["library_id"]]
                    source = source.resolve()
                    if not source.is_relative_to(root):
                        continue
                    source = source.relative_to(root)
                if source.as_posix() != item["path"]:
                    continue
            found.append(item)
        return [self.entry_card(item["id"]) for item in sorted(found, key=self._order)]

    def _link_files(self, file):
        links = []
        for relation in file["links"]:
            target = relation["target"]
            if relation["kind"] == "include":
                path = PurePosixPath(file["path"])
                paths = {target, (path.parent / target).as_posix()}
                candidates = [i for i, candidate in self._files.items()
                              if candidate["path"] in paths or fnmatchcase(candidate["path"], "*/" + target)]
            else:
                stem = target.rsplit(".", 1)[-1]
                candidates = list(self._module_files.get(stem, ()))
                module_path = target.replace(".", "/") + ".v"
                exact = [i for i in candidates if self._files[i]["path"].endswith(module_path)]
                candidates = exact or candidates
            same_library = [i for i in candidates if self._files[i]["library_id"] == file["library_id"]]
            candidates = same_library or candidates
            links.append({**relation, "file_ids": sorted(candidates),
                          "status": "located" if len(candidates) == 1 else "ambiguous" if candidates else "unresolved"})
        return links

    def related_entries(self, entry_id, limit=20):
        item = self._entry(entry_id)
        file = self._files[item["file_id"]]
        local_links = self._link_files(file)
        accessible_ids = {fid for edge in local_links for fid in edge["file_ids"]}
        frontier = list(accessible_ids)
        while frontier:
            fid = frontier.pop()
            for edge in self._link_files(self._files[fid]):
                through_c = self._files[fid]["format"] in {".c", ".h"}
                if not through_c and edge["kind"] not in {"Export", "Require Export"}:
                    continue
                for target in edge["file_ids"]:
                    if target != file["id"] and target not in accessible_ids:
                        accessible_ids.add(target)
                        frontier.append(target)
        resolved = {}
        for symbol in sorted(self._entry_symbols[entry_id]):
            candidates = [self._entries[i] for i in self._symbols.get(symbol, ())
                          if i != entry_id and self._entries[i]["kind"] == "rocq_declaration"]
            qualified = "." in symbol
            scopes = item.get("scope", [])
            by_scope = [candidate for candidate in candidates if candidate["scope"] == scopes
                        and candidate["file_id"] == file["id"]]
            visible = [candidate for candidate in candidates if candidate["file_id"] in accessible_ids
                       or candidate["file_id"] == file["id"]]
            chosen = candidates if qualified else (by_scope or visible or candidates)
            for candidate in chosen:
                resolved[candidate["id"]] = {"relation": "symbol_reference", "symbol": symbol,
                    "status": ("located" if len(chosen) == 1 and (qualified or candidate in visible)
                               else "candidate")}
        if item["kind"] == "c_contract_reference":
            for candidate in self.find_contracts(item["name"], item["library_id"], item["path"]):
                if candidate["structure"]["branch"] == item["structure"]["branch"]:
                    resolved[candidate["id"]] = {"relation": "named_contract", "status": "located"}
        own = item["structure"].get("declaration_start")
        for identifier in self._entries_by_file[file["id"]]:
            candidate = self._entries[identifier]
            if (candidate["kind"] == "proof" and candidate["structure"]["declaration_start"] == item["start"]
                    or own is not None and candidate["start"] == own):
                resolved[identifier] = {"relation": "proof_span", "status": "located"}
        if item["kind"] == "rocq_declaration":
            name = normalize_symbol(item["qualified_name"])
            mentions = self._mentions.get(name, set()) | self._mentions.get(item["name"], set())
            for identifier in mentions:
                candidate = self._entries[identifier]
                if candidate["kind"] == "proof" and identifier not in resolved:
                    resolved[identifier] = {"relation": "historical_mention", "symbol": name, "status": "candidate"}
        order = {"proof_span": 0, "named_contract": 1, "symbol_reference": 2, "historical_mention": 3}
        ranked = sorted(resolved, key=lambda i: (order[resolved[i]["relation"]],
                        resolved[i]["status"] != "located", self._order(self._entries[i])))
        output = page(ranked, "entries", limit, 0)
        output["entries"] = [{**self.entry_card(i), **resolved[i]} for i in output["entries"]]
        return {**output, "links": local_links,
                "scope": self._scope(accessible_ids | {file["id"]})}


def build_index(reference_libraries):
    return ReferenceIndex(reference_libraries)
