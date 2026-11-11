#!/usr/bin/env python3
"""Check that isolated QCP C files agree on function signatures and specs.

The SM2 verification splits callers and callees into independent annotated C
files.  This script treats declarations in those files as copies of one
interface and checks that:

* every parsed function declaration/definition has a QCP contract;
* all annotated occurrences of the same function have the same C signature;
* declarations in a definition's file form its complete base/derived contract;
* a caller declaration contains only canonical spec variants, except for an
  explicit ``derived <= base`` variant whose base is canonical and verified
  and whose caller-local derive VC has a completed proof;
* every call through a declaration with multiple specs explicitly selects a
  local spec tag with ``where (<tag>)``;
* optional spec_contract files agree with the definition-owned contract;
* explicit TODO-only entries in a spec_contract file are treated as future
  placeholders, while an unannotated or malformed entry still fails.

Whitespace and comments are ignored.  When copied spec bodies are compared,
a QCP spec tag (for example ``non_alias`` or ``r_eq_a``) is deliberately
ignored, as are alpha-renamings of variables bound by ``exists``/``forall``.
Tags are still checked locally when a multispec call selects a variant and to
validate proof-carrying caller-local derivations.  The remaining tokens from
``With``/``Require`` through ``Ensure`` are compared strictly.  Multiple specs
are compared as an unordered multiset.

The defaults are discovered relative to the repository containing this
script.  Paths can be overridden, so moving or consolidating the repository
does not require editing the checker:

    python3 test/spec_check.py
    python3 test/spec_check.py --source-root path/to/annotated_sources
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


ANNOTATION = "annotation"
IDENTIFIER = "identifier"
ATOM = "atom"

CONTROL_WORDS = {
    "if",
    "for",
    "while",
    "switch",
    "sizeof",
    "_Alignof",
    "__attribute__",
}

MULTI_CHAR_TOKENS = (
    ">>=",
    "<<=",
    "...",
    "|--",
    "->",
    "++",
    "--",
    "&&",
    "||",
    "<=",
    ">=",
    "==",
    "!=",
    "+=",
    "-=",
    "*=",
    "/=",
    "%=",
    "&=",
    "|=",
    "^=",
    "<<",
    ">>",
    "::",
    "##",
    "**",
)


class ParseError(RuntimeError):
    """Raised when a source file cannot be scanned safely."""


@dataclass(frozen=True)
class Token:
    kind: str
    value: str
    line: int


@dataclass(frozen=True)
class ContractSpec:
    tag: str | None
    derived_from: str | None
    body: tuple[str, ...]
    line: int
    is_todo: bool = False


@dataclass(frozen=True)
class FunctionOccurrence:
    name: str
    signature: tuple[str, ...]
    specs: tuple[ContractSpec, ...]
    path: Path
    line: int
    is_definition: bool
    is_contract: bool

    @property
    def spec_key(self) -> tuple[tuple[str, ...], ...]:
        """Tags, spec order, and quantified-variable names are irrelevant."""

        parameter_renaming = {
            original: canonical
            for _, original, canonical in function_parameter_bindings(
                self.signature, self.name
            )
        }
        return tuple(
            sorted(
                normalize_contract_body(
                    tuple(parameter_renaming.get(value, value) for value in spec.body)
                )
                for spec in self.specs
                if not spec.is_todo
            )
        )

    @property
    def complete_specs(self) -> tuple[ContractSpec, ...]:
        """Return only executable Require/Ensure contracts, not TODO markers."""

        return tuple(spec for spec in self.specs if not spec.is_todo)

    @property
    def signature_key(self) -> tuple[str, ...]:
        """Parameter names are not part of a C function type."""

        return normalize_function_signature(self.signature, self.name)

    @property
    def role(self) -> str:
        if self.is_contract:
            return "contract"
        return "callee definition" if self.is_definition else "caller declaration"


def _consume_quoted(text: str, start: int, line: int) -> tuple[int, int]:
    quote = text[start]
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char == quote:
            return index + 1, line
        if char == "\n":
            line += 1
        index += 1
    raise ParseError(f"unterminated {quote} literal at line {line}")


def lex_c(text: str) -> list[Token]:
    """Tokenize enough C syntax to identify top-level function declarations.

    Ordinary comments and preprocessor directive lines are discarded.
    ``/*@ ... */`` blocks are retained as single annotation tokens.
    """

    tokens: list[Token] = []
    index = 0
    line = 1
    line_start = 0
    length = len(text)

    while index < length:
        char = text[index]

        if char.isspace():
            if char == "\n":
                line += 1
                line_start = index + 1
            index += 1
            continue

        # A directive may contain a backslash-continued macro body.  Skip the
        # whole logical line so function-like macros are not parsed as C APIs.
        if char == "#" and not text[line_start:index].strip():
            while index < length:
                newline = text.find("\n", index)
                if newline < 0:
                    index = length
                    break
                continued_at = newline - 1
                if continued_at >= 0 and text[continued_at] == "\r":
                    continued_at -= 1
                continued = continued_at >= 0 and text[continued_at] == "\\"
                index = newline + 1
                line += 1
                line_start = index
                if not continued:
                    break
            continue

        if text.startswith("//", index):
            newline = text.find("\n", index + 2)
            if newline < 0:
                break
            index = newline
            continue

        if text.startswith("/*", index):
            end = text.find("*/", index + 2)
            if end < 0:
                raise ParseError(f"unterminated block comment at line {line}")
            raw = text[index + 2 : end]
            start_line = line
            if raw.startswith("@"):
                tokens.append(Token(ANNOTATION, raw[1:], start_line))
            consumed = text[index : end + 2]
            newline_count = consumed.count("\n")
            if newline_count:
                line += newline_count
                line_start = index + consumed.rfind("\n") + 1
            index = end + 2
            continue

        if char in {'"', "'"}:
            start_line = line
            end, line = _consume_quoted(text, index, line)
            tokens.append(Token(ATOM, text[index:end], start_line))
            if "\n" in text[index:end]:
                line_start = index + text[index:end].rfind("\n") + 1
            index = end
            continue

        if char.isalpha() or char == "_":
            end = index + 1
            while end < length and (text[end].isalnum() or text[end] == "_"):
                end += 1
            tokens.append(Token(IDENTIFIER, text[index:end], line))
            index = end
            continue

        if char.isdigit():
            end = index + 1
            while end < length and (
                text[end].isalnum() or text[end] in {"_", "."}
            ):
                end += 1
            tokens.append(Token(ATOM, text[index:end], line))
            index = end
            continue

        matched = next(
            (operator for operator in MULTI_CHAR_TOKENS if text.startswith(operator, index)),
            None,
        )
        if matched is not None:
            tokens.append(Token(ATOM, matched, line))
            index += len(matched)
            continue

        tokens.append(Token(ATOM, char, line))
        index += 1

    return tokens


def lex_annotation(text: str) -> tuple[str, ...]:
    """Normalize an annotation into a whitespace-independent token stream."""

    values: list[str] = []
    index = 0
    length = len(text)

    while index < length:
        char = text[index]
        if char.isspace():
            index += 1
            continue
        if text.startswith("//", index):
            newline = text.find("\n", index + 2)
            if newline < 0:
                break
            index = newline + 1
            continue
        if text.startswith("/*", index):
            end = text.find("*/", index + 2)
            if end < 0:
                raise ParseError("unterminated nested comment in annotation")
            index = end + 2
            continue
        if char in {'"', "'"}:
            end, _ = _consume_quoted(text, index, 1)
            values.append(text[index:end])
            index = end
            continue
        if char.isalpha() or char == "_":
            end = index + 1
            while end < length and (text[end].isalnum() or text[end] == "_"):
                end += 1
            values.append(text[index:end])
            index = end
            continue
        if char.isdigit():
            end = index + 1
            while end < length and (
                text[end].isalnum() or text[end] in {"_", "."}
            ):
                end += 1
            values.append(text[index:end])
            index = end
            continue
        matched = next(
            (operator for operator in MULTI_CHAR_TOKENS if text.startswith(operator, index)),
            None,
        )
        if matched is not None:
            values.append(matched)
            index += len(matched)
            continue
        values.append(char)
        index += 1

    return tuple(values)


def _is_identifier(value: str) -> bool:
    return bool(value) and (value[0].isalpha() or value[0] == "_") and all(
        char.isalnum() or char == "_" for char in value[1:]
    )


def _binder_positions(declaration: Sequence[str]) -> list[int]:
    """Return variable-token positions in a quantifier declaration.

    QCP accepts both untyped binders (``exists x y,``) and Coq-style typed
    groups (``forall (i j : Z),``).  In typed groups, identifiers after the
    colon belong to the type and must not be alpha-renamed.
    """

    if ":" not in declaration:
        return [
            index
            for index, value in enumerate(declaration)
            if _is_identifier(value)
        ]

    positions: set[int] = set()
    for colon in (
        index for index, value in enumerate(declaration) if value == ":"
    ):
        start = colon - 1
        while start >= 0 and declaration[start] not in {"(", ")", ","}:
            start -= 1
        positions.update(
            index
            for index in range(start + 1, colon)
            if _is_identifier(declaration[index])
        )
    return sorted(positions)


def alpha_normalize_quantifiers(tokens: Sequence[str]) -> tuple[str, ...]:
    """Canonicalize names introduced by annotation-level quantifiers.

    The QCP front end requires a caller's ``Given`` names to match a callee's
    existential binders, while generated Rocq may require a different name to
    avoid shadowing a type such as ``Z``.  These are alpha-equivalent specs, so
    the repository consistency check compares canonical binder names.
    """

    normalized = list(tokens)
    quantifier_index = 0
    index = 0

    while index < len(normalized):
        quantifier = normalized[index]
        if quantifier not in {"exists", "forall"}:
            index += 1
            continue

        depth = 0
        comma = None
        for cursor in range(index + 1, len(normalized)):
            value = normalized[cursor]
            if value == "(":
                depth += 1
            elif value == ")":
                depth -= 1
            elif value == "," and depth == 0:
                comma = cursor
                break
        if comma is None:
            index += 1
            continue

        declaration = normalized[index + 1 : comma]
        binder_positions = _binder_positions(declaration)
        renaming: dict[str, str] = {}
        for binder_index, position in enumerate(binder_positions):
            original = declaration[position]
            renaming.setdefault(
                original,
                f"<{quantifier}_{quantifier_index}_{binder_index}>",
            )

        for position in binder_positions:
            absolute = index + 1 + position
            normalized[absolute] = renaming[normalized[absolute]]
        for cursor in range(comma + 1, len(normalized)):
            replacement = renaming.get(normalized[cursor])
            if replacement is not None:
                normalized[cursor] = replacement

        quantifier_index += 1
        index = comma + 1

    return tuple(normalized)


def normalize_contract_body(tokens: Sequence[str]) -> tuple[str, ...]:
    """Normalize `With` binders and annotation-level quantifiers."""

    normalized = list(tokens)
    if "With" in normalized and "Require" in normalized:
        with_index = normalized.index("With")
        require_index = normalized.index("Require", with_index + 1)
        declaration = normalized[with_index + 1 : require_index]
        binder_positions = _binder_positions(declaration)
        renaming: dict[str, str] = {}
        binders: list[str] = []
        for binder_index, position in enumerate(binder_positions):
            original = declaration[position]
            canonical = f"<with_{binder_index}>"
            renaming.setdefault(original, canonical)
            binders.append(canonical)

        suffix = normalized[require_index:]
        suffix = [renaming.get(value, value) for value in suffix]
        normalized = normalized[: with_index + 1] + binders + suffix

    return alpha_normalize_quantifiers(normalized)


def function_parameter_bindings(
    tokens: Sequence[str], name: str
) -> list[tuple[int, str, str]]:
    """Return absolute positions and canonical names for C parameters."""

    values = list(tokens)
    try:
        name_index = values.index(name)
        open_index = values.index("(", name_index + 1)
    except ValueError:
        return []

    depth = 0
    close_index = None
    for index in range(open_index, len(values)):
        if values[index] == "(":
            depth += 1
        elif values[index] == ")":
            depth -= 1
            if depth == 0:
                close_index = index
                break
    if close_index is None:
        return []

    parameter_ranges: list[tuple[int, int]] = []
    start = open_index + 1
    paren_depth = 0
    bracket_depth = 0
    for index in range(start, close_index):
        value = values[index]
        if value == "(":
            paren_depth += 1
        elif value == ")":
            paren_depth -= 1
        elif value == "[":
            bracket_depth += 1
        elif value == "]":
            bracket_depth -= 1
        elif value == "," and paren_depth == 0 and bracket_depth == 0:
            parameter_ranges.append((start, index))
            start = index + 1
    parameter_ranges.append((start, close_index))

    bindings: list[tuple[int, str, str]] = []
    for parameter_index, (start, end) in enumerate(parameter_ranges):
        parameter = values[start:end]
        if parameter in ([], ["void"], ["..."]):
            continue
        array_start = parameter.index("[") if "[" in parameter else len(parameter)
        identifiers = [
            index
            for index, value in enumerate(parameter[:array_start])
            if _is_identifier(value)
        ]
        if len(identifiers) < 2:
            continue
        absolute = start + identifiers[-1]
        bindings.append(
            (absolute, values[absolute], f"<param_{parameter_index}>")
        )

    return bindings


def normalize_function_signature(
    tokens: Sequence[str], name: str
) -> tuple[str, ...]:
    """Canonicalize a function type, excluding declaration-only ``extern``."""

    normalized = list(tokens)
    for position, _, canonical in function_parameter_bindings(tokens, name):
        normalized[position] = canonical

    return tuple(token for token in normalized if token != "extern")


def parse_contract_annotation(token: Token) -> ContractSpec | None:
    values = lex_annotation(token.value)
    if not values:
        return None

    contract_heads = [
        index for index, value in enumerate(values) if value in {"With", "Require"}
    ]
    has_contract = "Require" in values and "Ensure" in values
    is_todo = not has_contract and values[-1] == "TODO"

    if not has_contract and not is_todo:
        return None

    if is_todo:
        body = ()
        tag_tokens = (
            () if values == ("Spec", ":", "TODO") else values[:-1]
        )
    elif contract_heads:
        body_start = min(contract_heads)
        tag_tokens = values[:body_start]
        body = values[body_start:]
    else:
        tag_tokens = ()
        body = values

    derived_from = None
    if "<=" in tag_tokens:
        relation_index = tag_tokens.index("<=")
        derived_from_tokens = tag_tokens[relation_index + 1 :]
        derived_from = (
            " ".join(derived_from_tokens) if derived_from_tokens else ""
        )
        tag_tokens = tag_tokens[:relation_index]
    tag = " ".join(tag_tokens) if tag_tokens else None
    return ContractSpec(
        tag=tag,
        derived_from=derived_from,
        body=body,
        line=token.line,
        is_todo=is_todo,
    )


def _matching_token(
    tokens: Sequence[Token],
    start: int,
    opening: str,
    closing: str,
    path: Path,
) -> int:
    depth = 0
    for index in range(start, len(tokens)):
        value = tokens[index].value
        if value == opening:
            depth += 1
        elif value == closing:
            depth -= 1
            if depth == 0:
                return index
    raise ParseError(
        f"{path}:{tokens[start].line}: unmatched {opening!r} while parsing"
    )


def _valid_function_prefix(prefix: Sequence[Token], name: str) -> bool:
    values = [token.value for token in prefix if token.kind != ANNOTATION]
    if not values or name in CONTROL_WORDS:
        return False
    if "typedef" in values or "=" in values:
        return False
    if any(value in {"(", ")"} for value in values):
        return False
    return any(token.kind == IDENTIFIER for token in prefix)


def parse_file(path: Path, *, is_contract: bool) -> list[FunctionOccurrence]:
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError as error:
        raise ParseError(f"{path}: source is not UTF-8: {error}") from error

    tokens = lex_c(text)
    occurrences: list[FunctionOccurrence] = []
    segment_start = 0
    index = 0

    while index < len(tokens):
        token = tokens[index]

        if token.value == ";":
            segment_start = index + 1
            index += 1
            continue

        if token.value == "{":
            close = _matching_token(tokens, index, "{", "}", path)
            segment_start = close + 1
            index = close + 1
            continue

        if (
            token.kind == IDENTIFIER
            and index + 1 < len(tokens)
            and tokens[index + 1].value == "("
        ):
            close_paren = _matching_token(tokens, index + 1, "(", ")", path)
            after = close_paren + 1
            annotations: list[Token] = []
            while after < len(tokens) and tokens[after].kind == ANNOTATION:
                annotations.append(tokens[after])
                after += 1

            if after < len(tokens) and tokens[after].value in {";", "{"}:
                prefix = [
                    item
                    for item in tokens[segment_start:index]
                    if item.kind != ANNOTATION
                ]
                if _valid_function_prefix(prefix, token.value):
                    signature_tokens = prefix + list(tokens[index : close_paren + 1])
                    specs = tuple(
                        spec
                        for annotation in annotations
                        if (spec := parse_contract_annotation(annotation)) is not None
                    )
                    is_definition = tokens[after].value == "{"
                    occurrences.append(
                        FunctionOccurrence(
                            name=token.value,
                            signature=tuple(item.value for item in signature_tokens),
                            specs=specs,
                            path=path,
                            line=token.line,
                            is_definition=is_definition,
                            is_contract=is_contract,
                        )
                    )

                    if is_definition:
                        close_brace = _matching_token(tokens, after, "{", "}", path)
                        segment_start = close_brace + 1
                        index = close_brace + 1
                    else:
                        segment_start = after + 1
                        index = after + 1
                    continue

            index = close_paren + 1
            continue

        index += 1

    return occurrences


def _where_tags(annotations: Sequence[Token]) -> list[str]:
    """Extract explicit ``where (<tag>)`` selectors from call annotations."""

    tags: list[str] = []
    for annotation in annotations:
        values = lex_annotation(annotation.value)
        index = 0
        while index < len(values):
            if (
                values[index] == "where"
                and index + 2 < len(values)
                and values[index + 1] == "("
            ):
                close = index + 2
                while close < len(values) and values[close] != ")":
                    close += 1
                if close < len(values):
                    tags.append(" ".join(values[index + 2 : close]))
                    index = close + 1
                    continue
            index += 1
    return tags


def check_multispec_call_tags(
    path: Path,
    occurrences: Sequence[FunctionOccurrence],
    repo_root: Path,
) -> list[str]:
    """Require an explicit valid tag at calls to locally declared multispecs."""

    multispec_tags: dict[str, set[str]] = {}
    specs_by_name: dict[str, list[ContractSpec]] = defaultdict(list)
    issues: list[str] = []

    for occurrence in occurrences:
        specs_by_name[occurrence.name].extend(occurrence.complete_specs)

    for name, specs in specs_by_name.items():
        if len(specs) <= 1:
            continue
        tags = [spec.tag for spec in specs]
        reference = next(
            occurrence for occurrence in occurrences if occurrence.name == name
        )
        if any(tag is None for tag in tags):
            issues.append(
                f"{name}: every variant of a multispec needs a tag at "
                f"{location(reference, repo_root)}"
            )
            continue
        concrete_tags = [tag for tag in tags if tag is not None]
        if len(set(concrete_tags)) != len(concrete_tags):
            issues.append(
                f"{name}: duplicate multispec tag at "
                f"{location(reference, repo_root)}"
            )
            continue
        multispec_tags[name] = set(concrete_tags)

    if not multispec_tags:
        return issues

    text = path.read_text(encoding="utf-8")
    tokens = lex_c(text)
    header_locations = {
        (occurrence.name, occurrence.line) for occurrence in occurrences
    }

    for index, token in enumerate(tokens):
        if (
            token.kind != IDENTIFIER
            or token.value not in multispec_tags
            or index + 1 >= len(tokens)
            or tokens[index + 1].value != "("
            or (token.value, token.line) in header_locations
        ):
            continue

        close = _matching_token(tokens, index + 1, "(", ")", path)
        annotations: list[Token] = []
        cursor = close + 1
        while cursor < len(tokens) and tokens[cursor].value not in {";", "{", "}"}:
            if tokens[cursor].kind == ANNOTATION:
                annotations.append(tokens[cursor])
            cursor += 1

        selected_tags = _where_tags(annotations)
        try:
            relative = path.relative_to(repo_root)
        except ValueError:
            relative = path
        call_location = f"{relative}:{token.line}"

        if not selected_tags:
            issues.append(
                f"{token.value}: multispec call at {call_location} must select "
                "a variant with where (<tag>)"
            )
            continue

        unknown_tags = sorted(
            set(selected_tags) - multispec_tags[token.value]
        )
        for tag in unknown_tags:
            issues.append(
                f"{token.value}: call at {call_location} selects unknown local "
                f"spec tag {tag!r}"
            )

    return issues


def _is_under_dot_git(path: Path) -> bool:
    return ".git" in path.parts


def discover_source_roots(repo_root: Path) -> list[Path]:
    roots = [
        path
        for path in repo_root.rglob("annotated_C")
        if path.is_dir() and not _is_under_dot_git(path)
    ]
    return sorted(set(roots))


def discover_contracts(repo_root: Path) -> list[Path]:
    contracts: list[Path] = []
    for name in ("spec_contract.c", "spec_contract.h"):
        contracts.extend(
            path
            for path in repo_root.rglob(name)
            if path.is_file() and not _is_under_dot_git(path)
        )
    return sorted(set(contracts))


def collect_source_files(source_roots: Iterable[Path]) -> list[Path]:
    files: set[Path] = set()
    for root in source_roots:
        if root.is_file():
            if root.suffix in {".c", ".h"}:
                files.add(root)
            continue
        for suffix in ("*.c", "*.h"):
            files.update(
                path
                for path in root.rglob(suffix)
                if path.is_file() and not _is_under_dot_git(path)
            )
    return sorted(files)


def resolve_paths(values: Sequence[str], repo_root: Path) -> list[Path]:
    paths: list[Path] = []
    for value in values:
        path = Path(value)
        if not path.is_absolute():
            path = repo_root / path
        paths.append(path.resolve())
    return paths


def location(occurrence: FunctionOccurrence, repo_root: Path) -> str:
    try:
        relative = occurrence.path.relative_to(repo_root)
    except ValueError:
        relative = occurrence.path
    return f"{relative}:{occurrence.line} ({occurrence.role})"


@dataclass(frozen=True)
class CaseArtifacts:
    goal: Path
    auto: Path
    manual: Path
    goal_check: Path


def locate_case_artifacts(
    repo_root: Path, source_path: Path
) -> CaseArtifacts | None:
    """Locate the generated VC family belonging to one isolated C case."""

    try:
        relative = source_path.relative_to(repo_root)
    except ValueError:
        relative = source_path

    if "annotated_C" in relative.parts:
        root_index = relative.parts.index("annotated_C")
        case_relative = Path(*relative.parts[root_index + 1 :]).with_suffix("")
        base = repo_root / "rocq" / "vc" / case_relative
        direct = CaseArtifacts(
            goal=base.with_name(base.name + "_goal.v"),
            auto=base.with_name(base.name + "_proof_auto.v"),
            manual=base.with_name(base.name + "_proof_manual.v"),
            goal_check=base.with_name(base.name + "_goal_check.v"),
        )
        if any(
            path.exists()
            for path in (direct.goal, direct.auto, direct.manual, direct.goal_check)
        ):
            return direct

    # The live QCP workspace keeps annotated sources and Rocq artifacts under
    # their deployed project paths rather than the archive's annotated_C/rocq
    # layout.  Resolve that canonical mapping before the recursive fallback so
    # scratch or migration copies under .tmp cannot make a proved callee look
    # ambiguous.
    qcp_prefix = ("QCP_examples", "Applications_human", "sm2")
    relative_parts = relative.parts
    for start in range(len(relative_parts) - len(qcp_prefix) + 1):
        if relative_parts[start : start + len(qcp_prefix)] != qcp_prefix:
            continue
        case_relative = Path(
            *relative_parts[start + len(qcp_prefix) :]
        ).with_suffix("")
        base = (
            repo_root
            / "Rocq"
            / "examples"
            / "Applications_human"
            / "sm2"
            / "vc"
            / case_relative
        )
        direct = CaseArtifacts(
            goal=base.with_name(base.name + "_goal.v"),
            auto=base.with_name(base.name + "_proof_auto.v"),
            manual=base.with_name(base.name + "_proof_manual.v"),
            goal_check=base.with_name(base.name + "_goal_check.v"),
        )
        if any(
            path.exists()
            for path in (direct.goal, direct.auto, direct.manual, direct.goal_check)
        ):
            return direct
        break

    # Support an explicitly supplied source root whose directory is not named
    # annotated_C.  Restrict the fallback to vc directories and the same module
    # name so identically named cases in experiments do not match accidentally.
    module_name = source_path.parent.name
    matches = [
        path
        for path in repo_root.rglob(source_path.stem + "_goal.v")
        if "vc" in path.parts and path.parent.name == module_name
    ]
    if len(matches) != 1:
        return None
    goal = matches[0]
    prefix = goal.name[: -len("_goal.v")]
    return CaseArtifacts(
        goal=goal,
        auto=goal.with_name(prefix + "_proof_auto.v"),
        manual=goal.with_name(prefix + "_proof_manual.v"),
        goal_check=goal.with_name(prefix + "_goal_check.v"),
    )


PROOF_BLOCK = re.compile(
    r"(?ms)^(?:Lemma|Theorem)\s+"
    r"(proof_of_[A-Za-z0-9_']+)\s*:\s*[A-Za-z0-9_']+\s*\.\s*"
    r"Proof\.(.*?)(Qed\.|Defined\.|Admitted\.|Abort\.)"
)


def completed_proofs(path: Path) -> set[str]:
    """Return proof names closed transparently or opaquely without a hole."""

    if not path.exists():
        return set()
    completed: set[str] = set()
    text = path.read_text(encoding="utf-8")
    for match in PROOF_BLOCK.finditer(text):
        name, body, terminator = match.groups()
        if terminator not in {"Qed.", "Defined."}:
            continue
        if re.search(r"\b(?:admit|Admitted)\b", body):
            continue
        completed.add(name)
    return completed


def artifact_location(path: Path, repo_root: Path) -> str:
    try:
        return str(path.relative_to(repo_root))
    except ValueError:
        return str(path)


def base_artifact_problem(
    repo_root: Path, definition: FunctionOccurrence
) -> str | None:
    """Check source-level evidence for the implementation-to-base proof."""

    artifacts = locate_case_artifacts(repo_root, definition.path)
    if artifacts is None:
        return "cannot locate the callee VC artifact family"
    missing = [
        path
        for path in (
            artifacts.goal,
            artifacts.auto,
            artifacts.manual,
            artifacts.goal_check,
        )
        if not path.exists()
    ]
    if missing:
        return "missing callee proof artifact(s): " + ", ".join(
            artifact_location(path, repo_root) for path in missing
        )

    manual_text = artifacts.manual.read_text(encoding="utf-8")
    if re.search(r"\bAdmitted\s*\.", manual_text):
        return (
            "callee manual proof still contains Admitted at "
            + artifact_location(artifacts.manual, repo_root)
        )

    goal_check_text = artifacts.goal_check.read_text(encoding="utf-8")
    expected_imports = (
        artifacts.goal.stem,
        artifacts.auto.stem,
        artifacts.manual.stem,
    )
    missing_imports = [
        name for name in expected_imports if name not in goal_check_text
    ]
    if missing_imports or "Module VC_Correctness : VC_Correct" not in goal_check_text:
        return (
            "callee goal check does not compose its goal/auto/manual artifacts at "
            + artifact_location(artifacts.goal_check, repo_root)
        )
    return None


def derived_artifact_problem(
    repo_root: Path,
    caller: FunctionOccurrence,
    witness: str,
) -> str | None:
    """Check that a caller-local derived contract has its own completed VC."""

    artifacts = locate_case_artifacts(repo_root, caller.path)
    if artifacts is None:
        return "cannot locate the caller VC artifact family"
    missing = [
        path
        for path in (
            artifacts.goal,
            artifacts.auto,
            artifacts.manual,
            artifacts.goal_check,
        )
        if not path.exists()
    ]
    if missing:
        return "missing caller proof artifact(s): " + ", ".join(
            artifact_location(path, repo_root) for path in missing
        )

    goal_text = artifacts.goal.read_text(encoding="utf-8")
    definition_pattern = re.compile(
        rf"(?m)^Definition\s+{re.escape(witness)}\s*:="
    )
    proof_name = "proof_of_" + witness
    axiom_pattern = re.compile(
        rf"(?m)^Axiom\s+{re.escape(proof_name)}\s*:\s*"
        rf"{re.escape(witness)}\s*\."
    )
    if not definition_pattern.search(goal_text) or not axiom_pattern.search(goal_text):
        return (
            f"derive VC {witness!r} is absent from "
            + artifact_location(artifacts.goal, repo_root)
        )

    proved = completed_proofs(artifacts.auto) | completed_proofs(artifacts.manual)
    if proof_name not in proved:
        return (
            f"derive VC {witness!r} has no Qed/Defined proof in "
            f"{artifact_location(artifacts.auto, repo_root)} or "
            f"{artifact_location(artifacts.manual, repo_root)}"
        )
    return None


def normalized_spec_body(
    occurrence: FunctionOccurrence, spec: ContractSpec
) -> tuple[str, ...]:
    parameter_renaming = {
        original: canonical
        for _, original, canonical in function_parameter_bindings(
            occurrence.signature, occurrence.name
        )
    }
    return normalize_contract_body(
        tuple(parameter_renaming.get(value, value) for value in spec.body)
    )


def with_specs(
    occurrence: FunctionOccurrence, specs: Sequence[ContractSpec]
) -> FunctionOccurrence:
    return FunctionOccurrence(
        name=occurrence.name,
        signature=occurrence.signature,
        specs=tuple(specs),
        path=occurrence.path,
        line=occurrence.line,
        is_definition=occurrence.is_definition,
        is_contract=occurrence.is_contract,
    )


def render_tokens(tokens: Sequence[str], limit: int = 360) -> str:
    rendered = " ".join(tokens)
    if len(rendered) <= limit:
        return rendered
    return rendered[: limit - 3] + "..."


def render_spec_delta(
    expected: Sequence[tuple[str, ...]],
    actual: Sequence[tuple[str, ...]],
) -> list[str]:
    expected_counter = Counter(expected)
    actual_counter = Counter(actual)
    missing = expected_counter - actual_counter
    extra = actual_counter - expected_counter
    lines: list[str] = []
    for body, count in missing.items():
        lines.append(f"      missing x{count}: {render_tokens(body)}")
    for body, count in extra.items():
        lines.append(f"      unexpected x{count}: {render_tokens(body)}")
    return lines


def compare_occurrences(
    expected: FunctionOccurrence,
    actual: FunctionOccurrence,
    repo_root: Path,
    *,
    allow_spec_subset: bool = False,
) -> list[str]:
    issues: list[str] = []
    if expected.signature_key != actual.signature_key:
        issues.extend(
            [
                f"{actual.name}: signature mismatch",
                f"    expected from {location(expected, repo_root)}:",
                f"      {render_tokens(expected.signature)}",
                f"    actual at {location(actual, repo_root)}:",
                f"      {render_tokens(actual.signature)}",
            ]
        )
    expected_specs = Counter(expected.spec_key)
    actual_specs = Counter(actual.spec_key)
    unexpected_specs = actual_specs - expected_specs
    spec_mismatch = (
        bool(unexpected_specs)
        if allow_spec_subset
        else expected_specs != actual_specs
    )
    if spec_mismatch:
        relation = (
            "caller spec is not a subset of the canonical contract"
            if allow_spec_subset
            else "spec mismatch"
        )
        issues.extend(
            [
                f"{actual.name}: {relation} (spec tags are already ignored)",
                f"    expected from {location(expected, repo_root)}",
                f"    actual at {location(actual, repo_root)}",
            ]
        )
        if allow_spec_subset:
            for body, count in unexpected_specs.items():
                issues.append(
                    f"      unexpected x{count}: {render_tokens(body)}"
                )
        else:
            issues.extend(render_spec_delta(expected.spec_key, actual.spec_key))
    return issues


def check_caller_contract_chain(
    reference: FunctionOccurrence,
    caller: FunctionOccurrence,
    local_specs: Sequence[ContractSpec],
    definition: FunctionOccurrence | None,
    repo_root: Path,
    base_artifact_cache: dict[Path, str | None],
) -> list[str]:
    """Check canonical copies plus proof-carrying caller-local derivations."""

    issues: list[str] = []
    derived_specs = [
        spec
        for spec in caller.complete_specs
        if spec.derived_from is not None
    ]
    ordinary_specs = [
        spec
        for spec in caller.complete_specs
        if spec.derived_from is None
    ]

    issues.extend(
        compare_occurrences(
            reference,
            with_specs(caller, ordinary_specs),
            repo_root,
            allow_spec_subset=True,
        )
    )
    if not derived_specs:
        return issues

    canonical_bodies = set(reference.spec_key)
    specs_by_tag: dict[str, list[ContractSpec]] = defaultdict(list)
    for spec in local_specs:
        if spec.is_todo:
            continue
        if spec.tag is not None:
            specs_by_tag[spec.tag].append(spec)

    base_problem: str | None
    if definition is None:
        base_problem = "callee has no verified definition in the current scope"
    else:
        if definition.path not in base_artifact_cache:
            base_artifact_cache[definition.path] = base_artifact_problem(
                repo_root, definition
            )
        base_problem = base_artifact_cache[definition.path]

    for derived in derived_specs:
        derived_tag = derived.tag
        base_tag = derived.derived_from
        derived_location = f"{location(caller, repo_root)} spec line {derived.line}"

        if not derived_tag or not _is_identifier(derived_tag):
            issues.append(
                f"{caller.name}: caller-local derived spec needs one identifier "
                f"as its derived tag at {derived_location}"
            )
            continue
        if not base_tag or not _is_identifier(base_tag):
            issues.append(
                f"{caller.name}: derived spec {derived_tag!r} needs one explicit "
                f"base tag after <= at {derived_location}"
            )
            continue

        base_candidates = specs_by_tag.get(base_tag, [])
        if len(base_candidates) != 1:
            issues.append(
                f"{caller.name}: derived spec {derived_tag!r} must name exactly "
                f"one local base spec {base_tag!r} at {derived_location}"
            )
            continue
        base_spec = base_candidates[0]
        if base_spec.derived_from is not None:
            issues.append(
                f"{caller.name}: derived spec {derived_tag!r} depends on another "
                f"caller-local derived spec {base_tag!r}; its base must be a "
                f"verified canonical callee spec at {derived_location}"
            )
            continue
        if normalized_spec_body(caller, base_spec) not in canonical_bodies:
            issues.append(
                f"{caller.name}: base spec {base_tag!r} for caller-local derived "
                f"spec {derived_tag!r} does not match any canonical callee "
                f"contract at {derived_location}"
            )
            continue
        if base_problem is not None:
            issues.append(
                f"{caller.name}: base spec {base_tag!r} for caller-local derived "
                f"spec {derived_tag!r} is not backed by a complete callee proof "
                f"artifact: {base_problem}"
            )
            continue

        witness = f"{caller.name}_derive_{derived_tag}_by_{base_tag}"
        derive_problem = derived_artifact_problem(repo_root, caller, witness)
        if derive_problem is not None:
            issues.append(
                f"{caller.name}: caller-local derived spec {derived_tag!r} is "
                f"not proved from base {base_tag!r} at {derived_location}: "
                f"{derive_problem}"
            )

    return issues


def check_repository(
    repo_root: Path,
    source_files: Sequence[Path],
    contract_files: Sequence[Path],
    *,
    require_contract: bool,
) -> tuple[list[str], list[str], int, int]:
    parse_issues: list[str] = []
    source_occurrences: list[FunctionOccurrence] = []
    contract_occurrences: list[FunctionOccurrence] = []
    source_occurrences_by_path: dict[Path, list[FunctionOccurrence]] = {}

    for path, is_contract, destination in (
        *((path, False, source_occurrences) for path in source_files),
        *((path, True, contract_occurrences) for path in contract_files),
    ):
        try:
            parsed = parse_file(path, is_contract=is_contract)
            destination.extend(parsed)
            if not is_contract:
                source_occurrences_by_path[path] = parsed
        except ParseError as error:
            parse_issues.append(str(error))

    if parse_issues:
        return parse_issues, [], len(source_occurrences), len(contract_occurrences)

    issues: list[str] = []
    notes: list[str] = []
    sources_by_name: dict[str, list[FunctionOccurrence]] = defaultdict(list)
    contracts_by_name: dict[str, list[FunctionOccurrence]] = defaultdict(list)

    for occurrence in source_occurrences:
        sources_by_name[occurrence.name].append(occurrence)
    for path, occurrences in source_occurrences_by_path.items():
        issues.extend(check_multispec_call_tags(path, occurrences, repo_root))
    for occurrence in contract_occurrences:
        contracts_by_name[occurrence.name].append(occurrence)

    canonical_contracts: dict[str, FunctionOccurrence] = {}
    base_artifact_cache: dict[Path, str | None] = {}
    todo_contract_names: list[str] = []
    for name, occurrences in contracts_by_name.items():
        reference = occurrences[0]
        all_specs = tuple(
            spec for occurrence in occurrences for spec in occurrence.specs
        )
        specs = tuple(spec for spec in all_specs if not spec.is_todo)
        for occurrence in occurrences[1:]:
            if reference.signature_key != occurrence.signature_key:
                issues.extend(compare_occurrences(reference, occurrence, repo_root))
        if not specs:
            if all_specs and all(spec.is_todo for spec in all_specs):
                todo_contract_names.append(name)
                continue
            issues.append(
                f"{name}: no Require/Ensure contract at "
                f"{location(reference, repo_root)}"
            )
            continue
        canonical_contracts[name] = FunctionOccurrence(
            name=name,
            signature=reference.signature,
            specs=specs,
            path=reference.path,
            line=reference.line,
            is_definition=False,
            is_contract=True,
        )

    external_names: list[str] = []
    for name, occurrences in sources_by_name.items():
        definitions = [occurrence for occurrence in occurrences if occurrence.is_definition]
        if not definitions:
            if name in canonical_contracts:
                reference = canonical_contracts[name]
                for occurrence in occurrences:
                    if not occurrence.complete_specs:
                        issues.append(
                            f"{name}: no Require/Ensure contract at "
                            f"{location(occurrence, repo_root)}"
                        )
                        continue
                    issues.extend(
                        check_caller_contract_chain(
                            reference,
                            occurrence,
                            tuple(
                                spec
                                for item in occurrences
                                if item.path == occurrence.path
                                for spec in item.specs
                            ),
                            None,
                            repo_root,
                            base_artifact_cache,
                        )
                    )
            else:
                external_names.append(name)
            continue

        if len(definitions) != 1:
            locations = ", ".join(location(item, repo_root) for item in definitions)
            issues.append(f"{name}: multiple annotated definitions: {locations}")
            continue

        definition = definitions[0]
        defining_occurrences = [
            occurrence for occurrence in occurrences if occurrence.path == definition.path
        ]
        defining_specs = tuple(
            spec
            for occurrence in defining_occurrences
            for spec in occurrence.complete_specs
        )
        local_reference = FunctionOccurrence(
            name=name,
            signature=definition.signature,
            specs=defining_specs,
            path=definition.path,
            line=definition.line,
            is_definition=True,
            is_contract=False,
        )

        if not defining_specs:
            issues.append(
                f"{name}: definition file has no Require/Ensure contract at "
                f"{location(definition, repo_root)}"
            )
            continue

        reference = canonical_contracts.get(name, local_reference)
        if require_contract and name not in canonical_contracts:
            issues.append(
                f"{name}: annotated function has no entry in a spec_contract file "
                f"(defined at {location(definition, repo_root)})"
            )
        if name in canonical_contracts:
            issues.extend(compare_occurrences(reference, local_reference, repo_root))

        for occurrence in occurrences:
            if occurrence.path == definition.path:
                if occurrence.signature_key != definition.signature_key:
                    issues.extend(compare_occurrences(definition, occurrence, repo_root))
                continue
            if not occurrence.complete_specs:
                issues.append(
                    f"{name}: no Require/Ensure contract at "
                    f"{location(occurrence, repo_root)}"
                )
                continue
            issues.extend(
                check_caller_contract_chain(
                    reference,
                    occurrence,
                    tuple(
                        spec
                        for item in occurrences
                        if item.path == occurrence.path
                        for spec in item.specs
                    ),
                    definition,
                    repo_root,
                    base_artifact_cache,
                )
            )

    if external_names:
        notes.append(
            "trusted external declarations (no definition in the current scope): "
            + ", ".join(sorted(external_names))
        )
    if todo_contract_names:
        notes.append(
            "explicit TODO-only spec_contract entries skipped: "
            + ", ".join(sorted(todo_contract_names))
        )

    return issues, notes, len(source_occurrences), len(contract_occurrences)


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Check C signatures and QCP specs across isolated annotated callers, "
            "callees, and spec_contract files."
        )
    )
    parser.add_argument(
        "--repo-root",
        help=(
            "repository root; defaults to the parent of the directory containing "
            "this script"
        ),
    )
    parser.add_argument(
        "--source-root",
        action="append",
        default=[],
        metavar="PATH",
        help=(
            "annotated source directory or file, relative to --repo-root; may be "
            "repeated. Defaults to recursively discovered annotated_C directories"
        ),
    )
    parser.add_argument(
        "--contract",
        action="append",
        default=[],
        metavar="PATH",
        help=(
            "spec_contract C/header file, relative to --repo-root; may be repeated. "
            "Defaults to recursively discovered spec_contract.c/spec_contract.h; "
            "the check also works without a central contract file"
        ),
    )
    parser.add_argument(
        "--require-contract",
        action="store_true",
        help="also fail when an annotated-only helper has no spec_contract entry",
    )
    parser.add_argument(
        "--quiet",
        action="store_true",
        help="suppress non-failing notes",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    arguments = build_argument_parser().parse_args(argv)
    script_root = Path(__file__).resolve().parent.parent
    repo_root = (
        Path(arguments.repo_root).resolve()
        if arguments.repo_root
        else script_root
    )

    source_roots = (
        resolve_paths(arguments.source_root, repo_root)
        if arguments.source_root
        else discover_source_roots(repo_root)
    )
    contract_files = (
        resolve_paths(arguments.contract, repo_root)
        if arguments.contract
        else discover_contracts(repo_root)
    )

    missing_paths = [
        path for path in (*source_roots, *contract_files) if not path.exists()
    ]
    if missing_paths:
        for path in missing_paths:
            print(f"[CONFIG] path does not exist: {path}", file=sys.stderr)
        return 2
    if not source_roots:
        print(
            "[CONFIG] no annotated source roots found; pass --source-root",
            file=sys.stderr,
        )
        return 2
    if arguments.require_contract and not contract_files:
        print(
            "[CONFIG] --require-contract needs at least one spec_contract file",
            file=sys.stderr,
        )
        return 2

    source_files = collect_source_files(source_roots)
    if not source_files:
        print(
            "[CONFIG] no .c or .h files found under the source roots",
            file=sys.stderr,
        )
        return 2

    issues, notes, source_count, contract_count = check_repository(
        repo_root,
        source_files,
        contract_files,
        require_contract=arguments.require_contract,
    )

    if issues:
        issue_count = sum(1 for issue in issues if not issue.startswith(" "))
        print(
            f"[FAIL] {issue_count} issue(s); checked "
            f"{source_count} annotated occurrence(s) and "
            f"{contract_count} contract occurrence(s)."
        )
        for issue in issues:
            print(issue)
        return 1

    if contract_count:
        contract_summary = (
            f" against {contract_count} contract occurrence(s)"
        )
    else:
        contract_summary = " using definition-owned contracts"
    print(
        f"[OK] checked {source_count} annotated occurrence(s) in "
        f"{len(source_files)} source file(s){contract_summary}."
    )
    if not arguments.quiet:
        for note in notes:
            print(f"[NOTE] {note}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
