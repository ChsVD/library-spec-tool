"""Dependency-first planning and scoped comparison contracts."""
from .contracts import (validate_plan, check_evidence, require_artifacts, nonempty,
                        safe_id, validate_review)


def validate_graph_plan(report, reader, reads, *, max_modules=24):
    errors = validate_plan(report, reader, reads, max_modules=max_modules)
    if not isinstance(report, dict) or not isinstance(report.get('modules'), list):
        return errors
    modules = {m['id']: m for m in report['modules'] if isinstance(m, dict) and safe_id(m.get('id'))}
    for ident, m in modules.items():
        for field in ('responsibilities', 'boundary', 'dependency_notes'):
            if not nonempty(m.get(field)):
                errors.append(f'{ident}.{field} required')
        if m.get('dependency_status') not in ('checked', 'unknown'):
            errors.append(f'{ident}.dependency_status must be checked/unknown')
        errors += check_evidence(m.get('evidence'), reader, libraries={m['library']})
        deps = m.get('dependencies')
        if not isinstance(deps, list):
            errors.append(f'{ident}.dependencies must be a list, even if empty')
            continue
        seen = set()
        for edge in deps:
            if not isinstance(edge, dict):
                errors.append('dependency must be an object'); continue
            dest = edge.get('prerequisite')
            if dest is not None and (not isinstance(dest, str) or dest not in modules):
                errors.append('dependency endpoint must be a planned module or null')
                continue
            if dest is not None and modules[dest]['library'] != m['library']:
                errors.append('cross-library similarity is not a dependency edge')
            if dest is None and not nonempty(edge.get('external')):
                errors.append('external dependency requires a name')
            kind = edge.get('kind')
            if kind not in ('call', 'representation', 'specification', 'build'):
                errors.append('invalid dependency kind')
            if edge.get('certainty') not in ('confirmed', 'unknown') or not nonempty(edge.get('reason')):
                errors.append('dependency requires certainty and reason')
            key = (dest, str(edge.get('external')), str(kind))
            if key in seen:
                errors.append('duplicate dependency edge')
            seen.add(key)
            errors += check_evidence(edge.get('evidence'), reader, libraries={m['library']})
    return errors


def dependency_frontier(plan):
    """A -> B means A requires B. No proof-completion state is inferred."""
    modules = {m['id']: m for m in plan['modules']}
    adjacent = {i: {e['prerequisite'] for e in m['dependencies']
                    if e['prerequisite'] and e['kind'] != 'build'} for i, m in modules.items()}
    reach = {}
    for ident in modules:
        found, todo = set(), list(adjacent[ident])
        while todo:
            node = todo.pop()
            if node not in found:
                found.add(node); todo.extend(adjacent[node] - found)
        reach[ident] = found
    cycles, handled = [], set()
    for ident in modules:
        if ident in reach[ident] and ident not in handled:
            group = sorted(j for j in modules if j in reach[ident] and ident in reach[j])
            handled.update(group); cycles.append(group)
    blocked, eligible = {}, []
    for ident, m in modules.items():
        if m['library'] != 'openssl': continue
        reasons = []
        if m['dependency_status'] != 'checked': reasons.append('dependency_inventory_unknown')
        for edge in m['dependencies']:
            if edge['certainty'] != 'confirmed' or edge['kind'] != 'build':
                reasons.append('unresolved_prerequisite:' + str(edge['prerequisite'] or edge['external']))
        if ident in reach[ident]: reasons.append('dependency_cycle')
        if reasons: blocked[ident] = reasons
        else: eligible.append(ident)
    impact = {i: sum(i in reach[j] for j, m in modules.items() if m['library'] == 'openssl' and j != i)
              for i in eligible}
    return {'edge_direction': 'dependent -> prerequisite', 'eligible': sorted(eligible, key=lambda i: (-impact[i], i)),
            'blocked': blocked, 'cycles': cycles, 'dependent_counts': impact,
            'proof_state': 'No target module is assumed proved; checked means planning inspection only.'}


def validate_selection(report, reader, reads, *, plan, frontier):
    errors = require_artifacts(reads, {'plan', 'dependency_frontier'})
    if not isinstance(report, dict): return errors + ['selection must be an object']
    primary = report.get('primary')
    if report.get('status') not in ('proposed', 'unable'):
        errors.append('selection status must be proposed/unable')
    if report.get('status') == 'unable':
        if primary is not None: errors.append('unable selection must have null primary')
    elif not isinstance(primary, str) or primary not in frontier['eligible']:
        errors.append('primary must be in the unblocked dependency frontier')
    for field in ('rationale', 'scope', 'blockers'):
        if not nonempty(report.get(field)): errors.append('selection.' + field + ' required')
    errors += check_evidence(report.get('evidence'), reader, libraries={'openssl'}, required=True)
    if primary in {m['id'] for m in plan['modules']}:
        module = next(m for m in plan['modules'] if m['id'] == primary)
        errors += check_evidence(module['evidence'], reader)
    return errors


def validate_screening(report, reader, reads, *, target, references):
    expected = {'card:' + m['id'] for m in [target] + references}
    errors = require_artifacts(reads, expected)
    if not isinstance(report, dict): return errors + ['screening must be an object']
    if report.get('target') != target['id']: errors.append('screening must use selected target')
    items = report.get('candidates')
    if not isinstance(items, list): return errors + ['screening candidates must be a list']
    ids = []
    for item in items:
        if not isinstance(item, dict): errors.append('candidate must be an object'); continue
        ids.append(item.get('reference'))
        if item.get('decision') not in ('match', 'no_match', 'unknown') or not nonempty(item.get('reason')):
            errors.append('screening requires decision and boundary-based reason')
    if sorted(map(str, ids)) != sorted(m['id'] for m in references):
        errors.append('screening must account for every reference card exactly once')
    return errors


def validate_pair(report, reader, reads, *, target, reference):
    errors = require_artifacts(reads, {'selection', 'screening', 'module:' + target['id'], 'module:' + reference['id']})
    if not isinstance(report, dict): return errors + ['comparison must be an object']
    if report.get('id') != 'pair-' + reference['id']: errors.append('comparison id must match assigned comparison_id')
    if report.get('target') != target['id'] or report.get('reference') != reference['id']:
        errors.append('comparison cannot switch selected target or screened reference')
    if report.get('relation') not in ('candidate', 'none', 'unknown'):
        errors.append('comparison relation must be candidate/none/unknown')
    for field in ('basis', 'differences', 'unknowns', 'representation', 'preconditions', 'dependencies', 'proof_status', 'adaptation'):
        if not nonempty(report.get(field)): errors.append('comparison.' + field + ' required')
    errors += check_evidence(report.get('evidence'), reader, libraries={'openssl', reference['library']})
    return errors


def validate_focused_review(report, reader, reads, *, plan, selection, screening, modules, comparisons):
    expected = {'plan', 'dependency_frontier', 'selection', 'screening'} | {'module:' + m['id'] for m in modules} | {'comparison:' + c['id'] for c in comparisons}
    errors = require_artifacts(reads, expected)
    # Reuse interval and blocking-finding checks, with the scoped module set.
    compatibility_reads = set(reads) | {'aggregate', 'comparison'}
    comparison = {'recommendation': {'primary': selection['primary']}, 'comparisons': comparisons}
    errors += validate_review(report, reader, compatibility_reads, modules=modules, comparison=comparison,
                              required_libraries={m['library'] for m in modules})
    if isinstance(report, dict) and report.get('verdict') == 'pass':
        chosen = next(m for m in plan['modules'] if m['id'] == selection['primary'])
        for evidence in [chosen['evidence'], selection['evidence']] + [e['evidence'] for e in chosen['dependencies']]:
            errors += check_evidence(evidence, reader)
        for module in modules:
            if module['depth'] != 'detailed': errors.append('scoped module must be detailed before review pass')
    return errors
