"""Role-specific structural and independently-read evidence checks."""
import re
from .report import SECTIONS, LIBRARIES, validate as validate_legacy


def nonempty(value):
    return isinstance(value, str) and bool(value.strip())


def safe_id(value):
    return isinstance(value, str) and re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,79}', value) is not None


def check_evidence(items, reader, *, libraries=None, required=True):
    errors, roots = [], set()
    if not isinstance(items, list) or (required and not items):
        return ['evidence must list independently read original file intervals']
    for item in items:
        try:
            path, start, end = item['path'], item['start'], item['end']
            if type(start) is not int or type(end) is not int or not 1 <= start <= end:
                raise ValueError('invalid interval')
            real = reader.path(path).relative_to(reader.root).as_posix()
            lines, sha = reader.lines(path)
            if end > len(lines):
                raise ValueError('line exceeds file')
            ranges = reader.reads.get(real, [])
            if not all(any(a <= n <= b and digest == sha for a, b, digest in ranges) for n in range(start, end+1)):
                raise ValueError('original evidence was not read by this role, or changed')
            roots.add(real.split('/')[0])
        except (KeyError, ValueError, TypeError, OSError, UnicodeError) as exc:
            errors.append('Invalid evidence: ' + str(exc))
    if libraries and not set(libraries) <= roots:
        errors.append('Independent evidence missing for libraries: ' + ', '.join(sorted(set(libraries) - roots)))
    return errors


def check_coverage(value):
    if not isinstance(value, dict):
        return ['coverage must describe the three libraries']
    return [f'coverage.{library}.{field} is required' for library in LIBRARIES
            for field in ('mapped_areas', 'unread_areas', 'configuration_unknowns')
            if not isinstance(value.get(library), dict) or not nonempty(value[library].get(field))]


def require_artifacts(reads, expected):
    missing = set(expected) - set(reads)
    return ['Derived artifacts must be inspected: ' + ', '.join(sorted(missing))] if missing else []


def validate_plan(report, reader, artifact_reads, *, max_modules=24):
    if not isinstance(report, dict):
        return ['planner report must be an object']
    errors = check_coverage(report.get('coverage')) + check_evidence(report.get('evidence'), reader, libraries=LIBRARIES)
    modules = report.get('modules')
    if not isinstance(modules, list) or not modules:
        return errors + ['modules must be a nonempty task list']
    if len(modules) > max_modules:
        errors.append(f'module_limit: {len(modules)} tasks exceeds max_modules={max_modules}; preserve plan, regroup with justification or stop, never omit tasks')
    ids, libraries = set(), set()
    for module in modules:
        if not isinstance(module, dict):
            errors.append('each module task must be an object')
            continue
        ident, library = module.get('id'), module.get('library')
        if not safe_id(ident) or ident in ids:
            errors.append('module IDs must be unique safe identifiers')
        ids.add(str(ident))
        if library not in LIBRARIES:
            errors.append('module library must be openssl/sm2/mini-gmp')
        libraries.add(str(library))
        for key in ('title', 'questions'):
            if not nonempty(module.get(key)):
                errors.append(f'{ident}.{key} is required')
        if not isinstance(module.get('scope'), list) or not module['scope']:
            errors.append(f'{ident}.scope must identify input paths')
        else:
            for path in module['scope']:
                try:
                    canonical = reader.path(path).relative_to(reader.root).as_posix()
                    if canonical.split('/')[0] != library:
                        raise ValueError('scope must belong to the task library')
                except (ValueError, OSError, TypeError) as exc:
                    errors.append(f'{ident}.scope: {exc}')
    if libraries != LIBRARIES:
        errors.append('planner must assign modules for all three libraries')
    return errors


def validate_module(report, reader, artifact_reads, *, task):
    if not isinstance(report, dict):
        return ['module report must be an object']
    errors = []
    for field in ('id', 'library'):
        if report.get(field) != task[field]:
            errors.append(f'module {field} must match assigned task')
    if not nonempty(report.get('title')) or report.get('depth') not in ('brief', 'detailed'):
        errors.append('module requires title and brief/detailed depth')
    sections = report.get('sections')
    for section in SECTIONS:
        if not isinstance(sections, dict) or not nonempty(sections.get(section)):
            errors.append('module section required: ' + section)
    errors += check_evidence(report.get('evidence'), reader, libraries={task['library']})
    return errors


def validate_aggregate(report, reader, artifact_reads, *, modules):
    if not isinstance(report, dict):
        return ['aggregate report must be an object']
    ids = {m['id'] for m in modules}
    errors = require_artifacts(artifact_reads, {'plan'} | {'module:' + ident for ident in ids})
    errors += check_coverage(report.get('coverage'))
    errors += check_evidence(report.get('evidence'), reader, required=False)
    if not isinstance(report.get('module_ids'), list) or set(report['module_ids']) != ids or len(report['module_ids']) != len(ids):
        errors.append('aggregate must account for every planned module exactly once')
    if report.get('readiness') not in ('ready', 'incomplete'):
        errors.append('aggregate readiness must be ready/incomplete')
    if not isinstance(report.get('gaps'), list) or not isinstance(report.get('rework'), list):
        return errors + ['gaps and rework must be lists, including explicit empty lists']
    for gap in report['gaps']:
        if (not isinstance(gap, dict) or gap.get('kind') not in ('omission', 'duplicate', 'conflict', 'unknown')
                or not nonempty(gap.get('description')) or type(gap.get('blocking')) is not bool
                or not isinstance(gap.get('module_ids'), list) or not set(gap['module_ids']) <= ids):
            errors.append('gap requires kind, description, known module_ids, and blocking boolean')
        elif gap['blocking'] and report.get('readiness') == 'ready':
            errors.append('blocking gaps cannot be ready')
    seen = set()
    for item in report['rework']:
        if not isinstance(item, dict) or item.get('module_id') not in ids or not nonempty(item.get('reason')):
            errors.append('rework must identify a planned module and concrete reason')
        elif item['module_id'] in seen:
            errors.append('rework module IDs must be unique')
        else:
            seen.add(item['module_id'])
    if report['rework'] and report.get('readiness') == 'ready':
        errors.append('pending worker rework cannot be ready')
    return errors


def validate_comparison(report, reader, artifact_reads, *, modules, aggregate):
    if not isinstance(report, dict):
        return ['comparison report must be an object']
    errors = require_artifacts(artifact_reads, {'aggregate'} | {'module:' + m['id'] for m in modules})
    if isinstance(report.get('recommendation'), dict) and 'primary' not in report['recommendation']:
        errors.append('recommendation.primary is required; use null when unable to recommend')
    # Existing validator checks IDs, relationships and recommendation structure.
    # Its module citation checks use previously validated artifacts; comparison
    # citations below must independently belong to the comparison role's reads.
    combined = {'coverage': aggregate['coverage'], 'modules': modules,
                'comparisons': report.get('comparisons'), 'recommendation': report.get('recommendation')}
    class ModuleEvidenceView:
        def __init__(self):
            self.root = reader.root
            self.reads = {path: list(ranges) for path, ranges in reader.reads.items()}
            for module in modules:
                for citation in module['evidence']:
                    path = reader.path(citation['path']).relative_to(reader.root).as_posix()
                    _, sha = reader.lines(path)
                    self.reads.setdefault(path, []).append((citation['start'], citation['end'], sha))
        path = reader.path
        lines = reader.lines
    errors += validate_legacy(combined, ModuleEvidenceView())
    if isinstance(report.get('comparisons'), list):
        libraries = {m['id']: m['library'] for m in modules}
        for comparison in report['comparisons']:
            if isinstance(comparison, dict):
                refs = {'openssl', libraries.get(comparison.get('reference'), '')}
                errors += check_evidence(comparison.get('evidence'), reader, libraries=refs)
    return errors


def validate_review(report, reader, artifact_reads, *, modules, comparison, required_libraries=None):
    if not isinstance(report, dict):
        return ['review report must be an object']
    ids = {m['id'] for m in modules}
    errors = require_artifacts(artifact_reads, {'aggregate', 'comparison'} | {'module:' + i for i in ids})
    errors += check_evidence(report.get('evidence'), reader, libraries=LIBRARIES if required_libraries is None else required_libraries)
    if report.get('verdict') not in ('pass', 'needs_revision', 'insufficient'):
        errors.append('review verdict must be pass/needs_revision/insufficient')
    if not isinstance(report.get('coverage_checked'), list) or set(report['coverage_checked']) != ids:
        errors.append('review must check every module, including unknown/unfinished areas')
    findings = report.get('findings')
    if not isinstance(findings, list):
        return errors + ['review findings must be a list']
    for finding in findings:
        if (not isinstance(finding, dict) or not safe_id(finding.get('id'))
                or finding.get('severity') not in ('blocking', 'nonblocking')
                or not nonempty(finding.get('description')) or not isinstance(finding.get('module_ids'), list)
                or not set(finding['module_ids']) <= ids):
            errors.append('review finding requires id/severity/description/known module_ids')
            continue
        errors += check_evidence(finding.get('evidence'), reader)
        if finding['severity'] == 'blocking' and report.get('verdict') == 'pass':
            errors.append('review pass cannot contain blocking findings')
    primary = comparison.get('recommendation', {}).get('primary')
    if report.get('verdict') == 'pass':
        for record in comparison.get('comparisons', []):
            comparison_errors = check_evidence(record.get('evidence'), reader)
            errors += ['Review must independently read every comparison interval: ' + e for e in comparison_errors]
    if report.get('verdict') == 'pass' and primary:
        primary_evidence = [e for m in modules if m['id'] == primary for e in m['evidence']]
        overlap = False
        for original in primary_evidence:
            for cited in report.get('evidence', []):
                try:
                    if (reader.path(original['path']) == reader.path(cited['path']) and
                            max(original['start'], cited['start']) <= min(original['end'], cited['end'])):
                        overlap = True
                except (KeyError, TypeError, ValueError, OSError):
                    pass
        if not overlap:
            errors.append('review evidence must overlap an original primary-module evidence interval, not merely the same file')
    return errors
