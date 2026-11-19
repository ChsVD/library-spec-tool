"""Scan Rocq source and rank the supported array entailment shapes."""

from hashlib import sha256
from pathlib import Path
import re

NAME = r"[\w']+(?:\.[\w']+)*"
LEX = re.compile(r'\(\*|\*\)|"(?:[^"]|"")*"|“|”|[()[\]{}]|\.(?=\s|$)')
DECL = re.compile(rf"(?:Local\s+)?(Module|End|Definition|Fixpoint|Lemma|Theorem|Fact|Remark|Corollary|Proposition)\s+({NAME})")
PRIMITIVES = {"store_array": "array.full", "store_array_missing_i_rec": "array.missing_index"}


def commands(text):
    """Yield exact source spans and blank comments/strings for structure recognition."""
    clean = list(text)
    stack = []
    comment = []
    begin = 0
    close = {"(": ")", "[": "]", "{": "}", "“": "”"}
    # Inside a comment, quotes have no effect on nested comment delimiters.
    token = re.compile(r"\(\*|\*\)")
    offset = 0
    while offset < len(text):
        match = (token if comment else LEX).search(text, offset)
        if not match:
            break
        offset = match.end()
        symbol = match[0]
        if symbol == "(*":
            comment.append(match.start())
        elif symbol == "*)" and comment:
            start = comment.pop()
            if not comment:
                clean[start:offset] = re.sub(r"[^\n]", " ", text[start:offset])
        elif comment:
            continue
        elif symbol.startswith('"'):
            clean[match.start():offset] = re.sub(r"[^\n]", " ", symbol)
        elif symbol in close:
            stack.append(close[symbol])
        elif stack and stack[-1] == symbol:
            stack.pop()
        elif symbol == "." and not stack:
            statement = "".join(clean[begin:offset])
            yield begin + len(statement) - len(statement.lstrip()), offset, statement.strip()
            begin = offset
    if comment:
        raise ValueError("unterminated Rocq comment")


TOKENS = re.compile(rf"{NAME}|:=|->|[|]--|\*\*|&&|[|][|]|[^\s]")


def split(text, operator):
    pieces = []
    stack = []
    close = {"(": ")", "[": "]", "{": "}", "“": "”"}
    start = 0
    for match in TOKENS.finditer(text):
        symbol = match[0]
        if not stack and symbol == operator:
            pieces.append(text[start:match.start()].strip())
            start = match.end()
        elif symbol in close:
            stack.append(close[symbol])
        elif stack and stack[-1] == symbol:
            stack.pop()
    return pieces + [text[start:].strip()]


def head(text):
    match = re.match(NAME, text)
    return match[0] if match else ""


def resolve(context, symbol, names):
    parent = context.rpartition(".")[0]
    scoped = f"{parent}.{symbol}"
    return scoped if parent and scoped in names else symbol


class ReferenceIndex:
    def __init__(self, path):
        path = Path(path)
        data = path.read_bytes()
        text = data.decode()
        self.digest = sha256(data).hexdigest()
        self.entries = {}
        definitions = {}
        scope = []
        for start, end, statement in commands(text):
            match = DECL.match(statement)
            if not match:
                continue
            kind, name = match.groups()
            body = statement[match.end():-1].strip()
            if kind == "Module":
                if not body:
                    scope.append(name)
                continue
            if kind == "End":
                if scope and scope[-1] == name:
                    scope.pop()
                continue
            name = ".".join([*scope, name])
            key = sha256(f"{path}:{self.digest}:{start}".encode()).hexdigest()[:24]
            self.entries[key] = {
                "id": key, "name": name, "kind": kind, "path": str(path),
                "digest": self.digest, "start": text.count("\n", 0, start) + 1,
                "end": text.count("\n", 0, end) + 1, "source": text[start:end],
                "structure": None,
            }
            if kind == "Definition":
                pieces = split(body, ":=")
                if len(pieces) == 2:
                    definitions[name] = pieces[1]
            elif kind != "Fixpoint":
                self.entries[key]["structure"] = body

        roles = {}
        for name, body in definitions.items():
            constructor = head(body)
            if constructor in PRIMITIVES:
                roles[name] = PRIMITIVES[constructor]
                storage = head(body[len(constructor):].strip())
                if storage:
                    roles[resolve(name, storage, definitions)] = "array.element"
        while True:
            inherited = {}
            for name, body in definitions.items():
                if name in roles:
                    continue
                matches = {
                    roles[symbol]
                    for branch in split(body, "||")
                    for term in split(branch, "&&")
                    if (symbol := resolve(name, head(term), roles)) in roles
                }
                if len(matches) == 1:
                    inherited[name] = matches.pop()
            if not inherited:
                break
            roles.update(inherited)
        for entry in self.entries.values():
            entry["structure"] = self._structure(entry["name"], entry["structure"], roles)

    @staticmethod
    def _structure(name, body, roles):
        if not body or not body.startswith(":"):
            return None
        expression = body[1:].strip()
        while re.match(r"forall\s", expression):
            parts = split(expression, ",")
            if len(parts) < 2:
                return None
            expression = ",".join(parts[1:]).strip()
        sides = split(expression, "|--")
        if len(sides) != 2:
            return None
        *premises, left = split(sides[0], "->")
        right = sides[1]
        left_roles, right_roles = (
            sorted({
                roles[symbol] for term in split(side, "**")
                if (symbol := resolve(name, head(term), roles)) in roles
            })
            for side in (left, right)
        )
        bounds = any(re.fullmatch(rf"0\s*<=\s*{NAME}\s*<\s*{NAME}", premise) for premise in premises)
        return {
            "left": left, "right": right, "premises": premises, "structure_status": "partial",
            "left_roles": left_roles, "right_roles": right_roles,
            "condition_roles": ["index.in_bounds"] if bounds else [],
        }

    def search(self, *, have, need, limit=5):
        have, need = set(have), set(need)
        cards = []
        for entry in self.entries.values():
            shape = entry["structure"]
            if shape is None:
                continue
            left = have.intersection(shape["left_roles"])
            right = need.intersection(shape["right_roles"])
            if not set(shape["left_roles"] + shape["right_roles"]).intersection(have | need):
                continue
            conditions = have.intersection(shape["condition_roles"])
            extra = len(shape["premises"]) > len(conditions)
            score = 4 * len(right) + 2 * (len(left) + len(conditions)) - int(extra)
            card = {key: entry[key] for key in ("id", "name", "path", "start", "end")}
            cards.append({**card, **shape, "score": score,
                          "have_match": sorted(left | conditions), "need_match": sorted(right)})
        return sorted(cards, key=lambda card: (-card["score"], card["start"]))[:limit]

    def read_entry(self, entry_id):
        return dict(self.entries[entry_id])

