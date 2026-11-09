"""Per-item review feedback; no partial result is an overall approval."""
from stage1.contracts import nonempty

def validate(report, proposal):
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
