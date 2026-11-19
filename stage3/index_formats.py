"""Static format readers for the production reference index."""

import re


SYMBOL = r"(?:[^\W\d]|_)[\w']*(?:(?:\.|::)(?:[^\W\d]|_)[\w']*)*"
SYMBOLS = re.compile(SYMBOL)
PAIRS = {"(": ")", "[": "]", "{": "}", "“": "”", "「": "」"}
OPERATORS = (":=", "->", "→", "<->", "↔", "|--", "|=", "⊢", "⊣⊢",
             "**", "&&", "\\/", "/\\", ":", ",", ";")
STRUCTURAL = re.compile("|".join(map(re.escape, sorted((*PAIRS, *PAIRS.values(),
                                                        *OPERATORS), key=len, reverse=True))))


def mask(text):
    return re.sub(r"[^\r\n]", " ", text)


def top_tokens(text):
    stack = []
    for match in STRUCTURAL.finditer(text):
        token = match[0]
        if token in PAIRS:
            stack.append(PAIRS[token])
        elif stack and stack[-1] == token:
            stack.pop()
        elif not stack:
            yield match


def split_top(raw, clean, *operators):
    parts, edges = [], []
    start = 0
    for match in top_tokens(clean):
        if match[0] in operators:
            parts.append((raw[start:match.start()], clean[start:match.start()]))
            start = match.end()
            edges.append(match[0])
    parts.append((raw[start:], clean[start:]))
    return parts, edges


def entry(kind, name, start, end, structure, **fields):
    return dict(kind=kind, name=name, start=start, end=end, structure=structure, **fields)


C_LEX = re.compile(r'/\*[\s\S]*?\*/|//[^\r\n]*|"(?:\\[\s\S]|[^"\\])*"|'
                   r"'(?:\\[\s\S]|[^'\\])*'|^[ \t]*\#[^\r\n]*(?:\r?\n(?<=\\\n)[^\r\n]*)*",
                   re.M)
C_EVENT = re.compile(r"[()\[\]{};,=]")
C_WORD = re.compile(r"[A-Za-z_]\w*")
C_ATTRIBUTE = re.compile(r"\b(?:__attribute__|__declspec|__asm__|asm|_Alignas|__extension__)\b")
C_CLAUSE = re.compile(r"\b(With|Require|Ensure)\b")
COQ_DIRECTIVE = re.compile(r"\b(Import|Extern)\s+Coq\b")
COQ_IMPORT = re.compile(
    rf"(?:From\s+(?P<prefix>{SYMBOL})\s+)?(?P<kind>Require(?:\s+(?:Import|Export))?|Import|Export)"
    rf"\s+(?P<modules>{SYMBOL}(?:\s+{SYMBOL})*)"
)
C_INCLUDE = re.compile(r'^\s*#\s*include\s*[<"]([^">]+)', re.M)


def module_links(statement):
    match = COQ_IMPORT.fullmatch(statement.strip())
    if not match:
        return []
    prefix = match.group("prefix")
    return [{"kind": match.group("kind"), "target": f"{prefix}.{name}" if prefix else name}
            for name in match.group("modules").split()]


def c_contract(raw):
    body = raw[3:-2].strip()
    clauses = list(C_CLAUSE.finditer(body))
    if not clauses or not any(clause[1] in {"Require", "Ensure"} for clause in clauses):
        return None
    branch = body[:clauses[0].start()].strip()
    if branch and not C_WORD.fullmatch(branch):
        return None
    structure = {"branch": branch or None, "with": None, "require": None, "ensure": None}
    for i, clause in enumerate(clauses):
        end = clauses[i + 1].start() if i + 1 < len(clauses) else len(body)
        structure[clause[1].lower()] = body[clause.end():end].strip()
    structure["status"] = "recognized" if structure["require"] and structure["ensure"] else "partial"
    return structure


def c_signature(clean, start, end, groups):
    candidates = []
    for opening, closing in groups:
        prefix = clean[start:opening]
        match = re.search(r"([A-Za-z_]\w*)\s*$", prefix)
        if not match or C_ATTRIBUTE.fullmatch(match[1]):
            continue
        before = prefix[:match.start()].strip()
        suffix = clean[closing:end].strip()
        if (before and re.search(r"[A-Za-z_]", before) and not re.search(r"[.=+/%?!:;]", before)
                and (not suffix or C_ATTRIBUTE.match(suffix))):
            candidates.append((match[1], start + len(prefix) - len(prefix.lstrip()), closing))
    return candidates[0] if len(candidates) == 1 else None


def parse_c(text):
    """Return (entries, file links). Character offsets slice the supplied text."""
    annotations, links = [], []
    clean_parts, cursor = [], 0
    for match in C_LEX.finditer(text):
        clean_parts.extend((text[cursor:match.start()], mask(match[0])))
        cursor = match.end()
        raw = match[0]
        if raw.startswith(("/*@", "//@")):
            comment = raw if raw.startswith("/*") else "/*@" + raw[3:] + "*/"
            annotations.append((match.start(), match.end(), comment))
        elif include := C_INCLUDE.match(raw):
            links.append({"kind": "include", "target": include[1]})
    clean_parts.append(text[cursor:])
    clean = "".join(clean_parts)

    result, groups, stack = [], [], []
    segment, annotation_index, outer_braces = 0, 0, 0
    initializer = False

    def process(end):
        nonlocal annotation_index
        signature = c_signature(clean, segment, end, groups) if not initializer else None
        while annotation_index < len(annotations) and annotations[annotation_index][0] < end:
            left, right, raw = annotations[annotation_index]
            annotation_index += 1
            if directive := COQ_DIRECTIVE.search(raw):
                body = raw[directive.end():-2].strip()
                imports = []
                if directive[1] == "Import":
                    imports = module_links(body.rstrip(".").strip())
                    if not imports and SYMBOLS.fullmatch(body.rstrip(".")):
                        imports = [{"kind": "Import", "target": body.rstrip(".")}]
                    links.extend(imports)
                result.append(entry("c_annotation", directive[0], left, right,
                                    {"status": "recognized", "directive": directive[0], "body": body},
                                    links=imports))
            elif spec := c_contract(raw):
                if left < segment or not signature:
                    result.append(entry("c_annotation", "Unbound contract", left, right,
                                        {**spec, "status": "unbound"}))
                    continue
                name, begin, closing = signature
                declaration = clean[begin:closing].strip()
                result.append(entry("contract", name, min(left, begin), max(right, closing),
                                    {**spec, "declaration": declaration},
                                    evidence_start=left, evidence_end=right,
                                    reference_text=" ".join(spec[clause] or "" for clause in ("require", "ensure"))))
            elif signature and C_WORD.fullmatch(raw[3:-2].strip()):
                name, begin, closing = signature
                if left >= segment:
                    result.append(entry("c_contract_reference", name, min(left, begin), max(right, closing),
                                        {"status": "named_reference", "branch": raw[3:-2].strip(),
                                         "declaration": clean[begin:closing].strip()},
                                        evidence_start=left, evidence_end=right))

    for match in C_EVENT.finditer(clean):
        token = match[0]
        if outer_braces:
            outer_braces += (token == "{") - (token == "}")
            if outer_braces == 0:
                segment = match.end()
                initializer = False
            continue
        if token in {"(", "["}:
            stack.append((token, match.start()))
        elif token in {")", "]"} and stack and PAIRS[stack[-1][0]] == token:
            opening, start = stack.pop()
            if not stack and opening == "(":
                groups.append((start, match.end()))
        elif not stack:
            if token == "=":
                initializer = True
            elif token in {";", "{"}:
                process(match.start())
                groups.clear()
                outer_braces = int(token == "{")
                initializer = False
                segment = match.end()
    groups.clear()
    process(len(text))
    return result, links


ROC_TOKEN = re.compile(r'\(\*|\*\)|"(?:""|[^"])*"|[()[\]{}“”「」]|\.(?=\s|\(\*|$)')
ROC_COMMENT = re.compile(r"\(\*|\*\)")
ROC_DECL = re.compile(
    rf"(?:#\[[^\]]*\]\s*|(?:Local|Global|Program|Polymorphic|Monomorphic|Cumulative|"
    rf"NonCumulative|Private)\s+)*(?P<kind>Definition|Let|Fixpoint|CoFixpoint|Lemma|"
    rf"Theorem|Fact|Remark|Corollary|Proposition|Example|Goal|Axiom|Axioms|Parameter|Parameters|"
    rf"Conjecture|Hypothesis|Hypotheses|Inductive|CoInductive|Variant|Record|Class|Instance|"
    rf"Equations|Scheme|Notation|Infix)\b(?:\s+(?P<name>{SYMBOL}))?"
)
ROC_SCOPE = re.compile(rf"(Module(?:\s+Type)?|Section|End)\s+(?:(?:Import|Export)\s+)?({SYMBOL})(.*)", re.S)
ROC_END = re.compile(r"(?:^|[}\n])\s*(?:[-+*]+\s+)*(Qed|Defined|Admitted|Abort|Save(?:\s+\w+)?)\s*\.$")
ROC_MARKER = re.compile(r"\(\*\s*-+\s*Function\s+([A-Za-z_]\w*)\s*-+\s*\*\)")
ROC_GENERATED = re.compile(r"\b(FuncSig|Spec|HoareFun)\b")
ROC_WITNESS = re.compile(r"_(?:wit|goal)_\d+(?:_|$)")
ROC_GENERATED_FILE = re.compile(r"_(?:goal(?:_check)?|proof(?:_auto|_manual)?(?:_part\d+)?)\.v$")
ROC_ENTAILS = ("|--", "|=", "⊢", "⊣⊢")
ROC_ARROW = ("->", "→", "<->", "↔")


def rocq_commands(text):
    clean = list(text)
    stack, comments = [], []
    begin = offset = 0
    while offset < len(text):
        match = (ROC_COMMENT if comments else ROC_TOKEN).search(text, offset)
        if not match:
            break
        token = match[0]
        offset = match.end()
        if token == "(*":
            comments.append(match.start())
        elif comments:
            start = comments.pop()
            if not comments:
                clean[start:offset] = mask(text[start:offset])
        elif token.startswith('"'):
            clean[match.start():offset] = mask(token)
        elif token in PAIRS:
            stack.append(PAIRS[token])
        elif stack and token == stack[-1]:
            stack.pop()
        elif token == "." and not stack:
            statement = "".join(clean[begin:offset])
            start = begin + len(statement) - len(statement.lstrip())
            if start < offset:
                yield start, offset, "".join(clean[start:offset]), True
            begin = offset
    if begin < len(text) and text[begin:].strip():
        if comments:
            clean[comments[0]:] = mask(text[comments[0]:])
        statement = "".join(clean[begin:])
        start = begin + len(statement) - len(statement.lstrip())
        if start < len(text):
            yield start, len(text), "".join(clean[start:]), False


def rocq_structure(raw, clean, kind):
    tokens = [match for match in top_tokens(clean) if match[0] in {":", ":="}]
    colon = tokens[0] if tokens and tokens[0][0] == ":" else None
    assign = next((match for match in tokens if match[0] == ":="), None)
    before = colon or assign
    name_binders = raw[:before.start()].strip() if before else ""
    structure = {"status": "unknown", "parameters": [name_binders] if name_binders else []}
    if colon:
        structure["type"] = raw[colon.end():assign.start() if assign else len(raw)].strip()
    if before:
        offset = (assign or colon).end()
        raw, clean = raw[offset:], clean[offset:]
    elif kind != "Goal":
        return structure
    while re.match(r"\s*forall\b", clean):
        binders, separators = split_top(raw, clean, ",")
        if not separators:
            return structure
        structure["parameters"].append(re.sub(r"^\s*forall\b", "", binders[0][0]).strip())
        offset = len(binders[0][0]) + 1
        raw, clean = raw[offset:], clean[offset:]
    statements, operators = split_top(raw, clean, *ROC_ENTAILS, *ROC_ARROW, "\\/", "/\\")
    if "\\/" in operators or "/\\" in operators:
        return structure
    entailments = [i for i, token in enumerate(operators) if token in ROC_ENTAILS]
    if len(entailments) == 1 and entailments[0] == len(operators) - 1:
        *premises, left, right = [part[0].strip() for part in statements]
        structure.update(status="partial", premises=premises, conclusion=right,
                         operator=operators[-1], left=left, right=right)
        for side, pair in zip(("left", "right"), statements[-2:]):
            terms, _ = split_top(*pair, "**")
            structure[f"{side}_resources"] = [term[0].strip() for term in terms]
    elif operators and all(op in {"->", "→"} for op in operators):
        *premises, conclusion = [part[0].strip() for part in statements]
        structure.update(status="partial", premises=premises, conclusion=conclusion,
                         operator=operators[-1])
    elif len(operators) == 1 and operators[0] in {"<->", "↔"}:
        structure.update(status="partial", operator=operators[0],
                         left=statements[0][0].strip(), right=statements[1][0].strip())
    return structure


def parse_rocq(text):
    result, links, scope = [], [], []
    markers = iter(ROC_MARKER.finditer(text))
    marker = next(markers, None)
    function = None
    pending, proof_begin = None, None
    for start, end, clean, complete in rocq_commands(text):
        while marker and marker.start() < start:
            function = marker[1]
            marker = next(markers, None)
        command = clean[:-1].strip() if complete else clean.strip()
        if pending and (termination := ROC_END.search(clean.strip())):
            pending["structure"]["proof_ending"] = termination[1]
            body_start = proof_begin if proof_begin is not None else start
            if body_start < end:
                result.append(entry("proof", pending["name"], body_start, end,
                                    {"status": "historical", "ending": termination[1],
                                     "declaration_start": pending["start"]}))
            pending, proof_begin = None, None
            continue
        if imported := module_links(command):
            links.extend(imported)
            result.append(entry("rocq_import", command, start, end,
                                {"status": "recognized"}, links=imported))
        elif scoped := ROC_SCOPE.fullmatch(command):
            kind, name, tail = scoped.groups()
            if kind == "End":
                if scope and scope[-1][1] == name:
                    scope.pop()
            elif ":=" not in tail and not tail.strip().startswith("with "):
                scope.append((kind, name))
        elif declaration := ROC_DECL.match(command):
            category, name = declaration.groups()
            if not name:
                name = category
            if category == "Goal":
                body_start = declaration.start("name") if declaration["name"] else declaration.end()
                name = "Goal"
            else:
                body_start = declaration.end()
            raw = text[start + body_start:end - int(complete)]
            body = clean[body_start:len(clean) - int(complete)]
            structure = rocq_structure(raw, body, category) if complete else {"status": "unknown"}
            generated = sorted(set(ROC_GENERATED.findall(body)))
            if generated:
                structure["generated_forms"] = generated
            if function:
                structure["generated_function_context"] = function
            qualified = ".".join([*(n for k, n in scope if k != "Section"), name])
            current = entry("rocq_declaration", name, start, end, structure,
                            declaration_kind=category, qualified_name=qualified,
                            scope=[n for _, n in scope], reference_text=body)
            result.append(current)
            proof_begin = None
            if category in {"Lemma", "Theorem", "Fact", "Remark", "Corollary", "Proposition", "Example", "Goal"}:
                pending = current
            elif category in {"Definition", "Instance", "Equations"}:
                pending = current if not any(m[0] == ":=" for m in top_tokens(body)) else None
            else:
                pending = None
        elif pending and proof_begin is None:
            proof_begin = start
    return result, links


STRATEGY_COMMENT = re.compile(r"/\*[\s\S]*?\*/|//[^\r\n]*")
RULE = re.compile(r"^[ \t]*id\s*:\s*(\d+)\b", re.M)
RULE_FIELD = re.compile(r"^[ \t]*(priority|left|right|check|action)\s*:", re.M)
ACTION = re.compile(r"(left|right)_(erase|add|exist_add)\s*\((.*)\)", re.S)


def parse_strategies(text):
    clean = STRATEGY_COMMENT.sub(lambda match: mask(match[0]), text)
    rules = list(RULE.finditer(clean))
    result = []
    for index, rule in enumerate(rules):
        end = rules[index + 1].start() if index + 1 < len(rules) else len(text)
        end = rule.start() + len(clean[rule.start():end].rstrip())
        fields = list(RULE_FIELD.finditer(clean, rule.end(), end))
        structure = {"status": "recognized", "rule_number": int(rule[1]), "priority": None,
                     "left": [], "right": [], "check": [], "action": [], "operations": []}
        for field_index, field in enumerate(fields):
            stop = fields[field_index + 1].start() if field_index + 1 < len(fields) else end
            name, value = field[1], text[field.end():stop].strip()
            if name == "priority":
                structure[name] = value
            else:
                structure[name].append(value)
            if name == "action":
                parts, _ = split_top(text[field.end():stop], clean[field.end():stop], ";")
                for raw_action, clean_action in parts:
                    if not clean_action.strip():
                        continue
                    operation = ACTION.fullmatch(clean_action.strip())
                    if operation:
                        side, action, _ = operation.groups()
                        argument = raw_action.strip().partition("(")[2].rpartition(")")[0].strip()
                        structure["operations"].append({"side": side, "operation": action,
                                                        "argument": argument})
                    else:
                        structure["status"] = "partial"
                        structure["operations"].append({"raw": raw_action.strip(), "operation": "unknown"})
        if not fields or not structure["action"]:
            structure["status"] = "unknown"
        result.append(entry("strategy", f"id {rule[1]}", rule.start(), end, structure))
    return result, [{"kind": "include", "target": match[1]} for match in C_INCLUDE.finditer(clean)]
