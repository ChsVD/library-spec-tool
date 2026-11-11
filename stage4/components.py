"""Per-item review feedback; no partial result is an overall approval."""
from stage1.contracts import nonempty

def validate(report, proposal):
    if proposal.get('protocol_version') == 3:
        return validate_v3(report, proposal)
    rows=report.get("item_reviews")
    if not isinstance(rows,list):return ["item_reviews required"]
    items={i["id"]:i for i in proposal["items"]}
    seen={};errors=[]
    for row in rows:
        if not isinstance(row,dict):errors.append("invalid item review");continue
        ident=row.get("item_id")
        if not isinstance(ident,str) or ident not in items or ident in seen:
            errors.append("item_reviews must cover each candidate exactly once");continue
        verdict=row.get("verdict");seen[ident]=verdict
        if verdict not in ("pass","needs_revision","insufficient"):errors.append("invalid item verdict")
        if not nonempty(row.get("reason")):errors.append("item review reason required")
        if row.get("action") not in ("retain","revise","add_material"):errors.append("invalid corrective action")
        expected={"pass":"retain","needs_revision":"revise","insufficient":"add_material"}
        if expected.get(verdict)!=row.get("action"):errors.append("item verdict/action mismatch")
        if verdict=="insufficient" and not nonempty(row.get("material_needed")):
            errors.append("insufficient item must describe missing material")
    if set(seen)!=set(items):errors.append("review all candidate IDs")
    for ident, verdict in seen.items():
        if verdict=="pass" and any(seen.get(dep)!="pass" for dep in items[ident]["depends_on"]):
            errors.append("passed item depends on unaccepted item")
    for unknown in proposal.get("unknowns",[]):
        if unknown.get("blocking"):
            affected=unknown.get("item_ids",list(items))
            if not isinstance(affected,list) or not affected or any(i not in items for i in affected):
                errors.append("blocking unknown has invalid item_ids")
            elif any(seen.get(i)=="pass" for i in affected):
                errors.append("passed item retains blocking unknown")
    for row in proposal.get("coverage",{}).values():
        for need in row.get("needs",[]):
            if need.get("unresolved"):
                affected=need.get("item_ids") or list(items)
                if any(seen.get(i)=="pass" for i in affected):
                    errors.append("passed item retains unresolved need")
    if report.get("verdict")=="partial" and (not any(v=="pass" for v in seen.values()) or all(v=="pass" for v in seen.values())):
        errors.append("partial requires both accepted and unaccepted items")
    if report.get("verdict")=="pass" and any(v!="pass" for v in seen.values()):
        errors.append("overall pass requires all items pass")
    # Unassigned blocking findings cannot be hidden by component reporting.
    for finding in report.get("findings",[]):
        if finding.get("blocking"):
            affected=finding.get("item_ids")
            if not isinstance(affected,list) or not affected or any(i not in items for i in affected):
                errors.append("blocking finding requires affected item_ids")
            elif any(seen.get(i)=="pass" for i in affected):
                errors.append("blocking finding affects passed item")
    return errors


def validate_v3(report, proposal):
    """Review source interpretation separately from each function's use judgment."""
    errors, verdicts = [], {}
    for field, key, objects in (
            ('reference_reviews', 'reference_id', proposal.get('references', [])),
            ('use_reviews', 'use_id', proposal.get('uses', []))):
        ids = {obj['id'] for obj in objects}
        rows = report.get(field)
        seen = {}
        if not isinstance(rows, list): errors.append(field + ' list required'); rows = []
        for row in rows:
            if not isinstance(row, dict): errors.append('review row object required'); continue
            ident = row.get(key)
            if not isinstance(ident, str) or ident not in ids or ident in seen:
                errors.append(field + ' must cover each ID exactly once'); continue
            value = row.get('verdict')
            seen[ident] = value
            if value not in ('pass', 'needs_revision', 'insufficient'): errors.append('invalid component verdict')
            if not nonempty(row.get('reason')): errors.append('component review reason required')
        if set(seen) != ids: errors.append(field + ' must cover each ID exactly once')
        verdicts[field] = seen
    refs, uses = verdicts['reference_reviews'], verdicts['use_reviews']
    for use in proposal.get('uses', []):
        if uses.get(use['id']) == 'pass' and any(refs.get(i) != 'pass' for i in use.get('reference_ids', [])):
            errors.append('accepted use depends on unaccepted reference: ' + use['id'])
    values = list(refs.values()) + list(uses.values())
    if report.get('verdict') == 'pass' and any(v != 'pass' for v in values):
        errors.append('overall pass requires all reference/use judgments pass')
    if report.get('verdict') == 'partial' and (not any(v == 'pass' for v in values) or not any(v != 'pass' for v in values)):
        errors.append('partial requires accepted and unaccepted judgments')
    findings = report.get('findings')
    if not isinstance(findings, list): return errors + ['findings list required']
    for finding in findings:
        if not isinstance(finding, dict) or not nonempty(finding.get('description')) or type(finding.get('blocking')) is not bool:
            errors.append('invalid finding'); continue
        rids, uids = finding.get('reference_ids', []), finding.get('use_ids', [])
        valid = (isinstance(rids, list) and isinstance(uids, list)
                 and all(isinstance(i, str) and i in refs for i in rids)
                 and all(isinstance(i, str) and i in uses for i in uids))
        if not valid: errors.append('finding must identify existing reference/use IDs'); continue
        if finding['blocking']:
            if not rids and not uids: errors.append('blocking finding requires affected reference_ids or use_ids')
            if any(refs[i] == 'pass' for i in rids) or any(uses[i] == 'pass' for i in uids):
                errors.append('blocking finding affects accepted judgment')
            if report.get('verdict') == 'pass': errors.append('blocking finding cannot pass')
    return errors
