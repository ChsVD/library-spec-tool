"""Structural planning records; no semantic proof or execution claims."""
from stage1.contracts import nonempty, safe_id, check_evidence

VERSION = 3


def candidate_digest(report):
    """Bind independent judgments to the entire exact candidate, including version."""
    from stage2.graph import digest
    return digest(report)


def common_need_ids(node, extract):
    return ['upstream-' + str(i) for i, _ in enumerate(node['spec'].get('common_needs', []))] + [
        n['id'] for n in extract.get('needs', [])]
FACETS = ("definition", "properties", "boundaries", "usage", "environment")
ACTIONS = ("reuse", "adapt", "supplement", "new", "not_needed", "unknown")


def requirements(report):
    if report.get('protocol_version') == 3:
        return requirements_v3(report)
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
    if report.get('protocol_version') == 3:
        return records_v3(report, reader)
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


def requirements_v3(report):
    errors, seen = [], set()
    for need in report.get('needs', []):
        if not isinstance(need, dict):
            errors.append('need object required'); continue
        ident = need.get('id')
        if not safe_id(ident) or ident in seen or str(ident).startswith('upstream-'):
            errors.append('extracted need requires unique stable non-upstream id')
        if isinstance(ident, str): seen.add(ident)
        for key in ('function_id', 'spec_clause', 'use_site', 'search_question'):
            if not nonempty(need.get(key)): errors.append('need field required: ' + key)
        if need.get('source') not in ('spec_extracted', 'upstream'):
            errors.append('need source must be spec_extracted or upstream')
    return errors


def records_v3(report, reader):
    """A reference is a source fact; a use is an explicitly unvalidated judgment."""
    from .strategies import validate
    errors = validate(report, reader)
    if not report.get('reference_strategies'):
        search = report.get('strategy_search')
        if not isinstance(search, dict) or not nonempty(search.get('reason')):
            errors.append('empty strategy attachment requires strategy_search.reason')
        elif 'evidence' in search:
            errors += check_evidence(search['evidence'], reader, required=False)
    refs = {}
    references = report.get('references')
    if not isinstance(references, list):
        errors.append('references list required'); references = []
    for ref in references:
        if not isinstance(ref, dict): errors.append('reference object required'); continue
        ident = ref.get('id')
        if not safe_id(ident) or ident in refs: errors.append('unique safe reference id required')
        if isinstance(ident, str): refs[ident] = ref
        for key in ('name', 'meaning', 'premises'):
            if not nonempty(ref.get(key)): errors.append('reference field required: ' + key)
        errors += ['reference ' + str(ident) + ': ' + e for e in check_evidence(ref.get('evidence'), reader)]
    uses = report.get('uses')
    if not isinstance(uses, list): return errors + ['uses list required']
    seen = set()
    for use in uses:
        if not isinstance(use, dict): errors.append('use object required'); continue
        ident = use.get('id')
        if not safe_id(ident) or ident in seen: errors.append('unique safe use id required')
        if isinstance(ident, str): seen.add(ident)
        for key in ('function_id', 'need_id', 'purpose'):
            if not nonempty(use.get(key)): errors.append('use field required: ' + key)
        result = use.get('result')
        if result not in ('direct', 'adapt', 'idea', 'not_found', 'uncertain'):
            errors.append('invalid retrieval result')
        selected = use.get('reference_ids')
        if not isinstance(selected, list) or any(not isinstance(i, str) or i not in refs for i in selected):
            errors.append('use reference_ids must refer to existing references')
        elif result in ('direct', 'adapt', 'idea') and not selected:
            errors.append('direct/adapt/idea use requires reference_ids')
        if result == 'not_found' and selected: errors.append('not_found use cannot select references')
        if result in ('direct', 'adapt', 'idea') and not nonempty(use.get('adaptation')):
            errors.append('direct/adapt/idea requires explicit premise and adaptation differences (or none)')
        if result == 'uncertain' and not nonempty(use.get('uncertainty')):
            errors.append('uncertain use requires specific uncertainty')
        if result == 'not_found' and not nonempty(use.get('search_scope')):
            errors.append('not_found requires actual search_scope')
        errors += ['use ' + str(ident) + ' search: ' + e for e in check_evidence(
            use.get('search_evidence', []), reader, required=result == 'not_found')]
        if use.get('target_status') != 'not_validated':
            errors.append('target_status must be not_validated')
    linked = {ident for use in uses if isinstance(use, dict)
              and isinstance(use.get('reference_ids'), list)
              for ident in use['reference_ids'] if isinstance(ident, str)}
    if set(refs) - linked:
        errors.append('shared reference must be linked to a function use: ' + ', '.join(sorted(set(refs) - linked)))
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
