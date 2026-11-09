"""Structural planning records; no semantic proof or execution claims."""
from stage1.contracts import nonempty, safe_id, check_evidence

VERSION = 2
FACETS = ("definition", "properties", "boundaries", "usage", "environment")
ACTIONS = ("reuse", "adapt", "supplement", "new", "not_needed", "unknown")


def requirements(report):
    errors = []
    seen = set()
    for need in report.get("needs", []):
        if not isinstance(need, dict):
            continue
        ident = need.get("id")
        if not safe_id(ident) or ident in seen:
            errors.append("need requires unique stable id")
        if isinstance(ident, str):
            seen.add(ident)
        for key in ("spec_clause", "use_site"):
            if not nonempty(need.get(key)):
                errors.append("need field required: " + key)
        if need.get("scope") not in ("shared", "local", "unknown"):
            errors.append("need scope required")
    return errors


def records(report, reader):
    from .strategies import validate
    errors = validate(report, reader)
    references = report.get("references")
    if not isinstance(references, list):
        return ["references list required"]
    refs = {}
    for ref in references:
        if not isinstance(ref, dict):
            errors.append("reference object required"); continue
        ident = ref.get("id")
        if not safe_id(ident) or ident in refs:
            errors.append("unique reference id required")
        if isinstance(ident, str):
            refs[ident] = ref
        for key in ("name", "search_scope", "applicability"):
            if not nonempty(ref.get(key)):
                errors.append("reference field required: " + key)
        facets = ref.get("facets", {})
        for key in FACETS:
            facet = facets.get(key) if isinstance(facets, dict) else None
            if not isinstance(facet, dict):
                errors.append("reference facet required: " + key); continue
            if facet.get("status") not in ("read", "not_found", "not_applicable", "unknown"):
                errors.append("invalid reference facet status")
            if not nonempty(facet.get("reason")):
                errors.append("reference facet reason required")
            errors += check_evidence(facet.get("evidence"), reader, required=facet.get("status") == "read")
    for row in report.get("coverage", {}).values():
        if not isinstance(row, dict): continue
        mappings = row.get("needs", [])
        if not isinstance(mappings, list): continue
        for mapping in mappings:
            if not isinstance(mapping, dict): continue
            action = mapping.get("action")
            if action not in ACTIONS:
                errors.append("need reuse action required")
            selected = mapping.get("reference_ids")
            if not isinstance(selected, list) or any(not isinstance(x, str) or x not in refs for x in selected):
                errors.append("need references must exist"); continue
            if action in ("reuse", "adapt", "supplement"):
                if not selected:
                    errors.append("reuse/adapt/supplement requires reference")
                for key in selected:
                    facets = refs[key].get("facets")
                    facet = facets.get("definition") if isinstance(facets, dict) else None
                    if not isinstance(facet, dict) or facet.get("status") != "read":
                        errors.append("selected reuse definition must be read")
            if action == "not_needed" and mapping.get("item_ids"):
                errors.append("not_needed cannot create items")
            if action == "unknown" and not nonempty(mapping.get("unresolved")):
                errors.append("unknown decision must retain unresolved")
            if action in ("reuse", "adapt", "supplement", "new") and not mapping.get("item_ids"):
                errors.append("resolved need must map to item")
    return errors


def obligations(item, reader):
    errors = []
    rows = item.get("validation_obligations")
    if not isinstance(rows, list) or not rows:
        return ["item requires validation_obligations"]
    ids = set()
    for row in rows:
        if not isinstance(row, dict):
            errors.append("validation obligation object required"); continue
        ident = row.get("id")
        if not safe_id(ident) or ident in ids:
            errors.append("unique obligation id required within item")
        if isinstance(ident, str): ids.add(ident)
        for key in ("kind", "purpose", "method", "environment", "success_criterion"):
            if not nonempty(row.get(key)):
                errors.append("validation obligation field required: " + key)
        if row.get("status") not in ("planned", "blocked", "not_applicable"):
            errors.append("planning cannot claim validation executed or passed")
        if row.get("status") in ("blocked", "not_applicable") and not nonempty(row.get("reason")):
            errors.append("blocked/not_applicable obligation needs reason")
        errors += check_evidence(row.get("evidence"), reader, required=False)
    if isinstance(rows, list) and rows and all(isinstance(r, dict) and r.get("status") == "not_applicable" for r in rows):
        errors.append("item requires an applicable validation obligation")
    return errors
