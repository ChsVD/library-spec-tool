"""Mechanical checks only; a passing report still requires human review."""
import json
import re

SECTIONS = ['模块职责与边界', '相关领域知识', '核心数据与表示', '主要操作及联系',
            '对外依赖与使用关系', '已有规约与证明材料', '阅读依据与待确认问题']
LIBRARIES = {'openssl', 'sm2', 'mini-gmp'}


def validate(report, reader):
    errors = []
    if not isinstance(report, dict):
        return ['Report must be an object']

    def text(value, label):
        if not isinstance(value, str) or not value.strip():
            errors.append(f'{label}: nonempty text required (explicit unknown is allowed)')

    def evidence(items, label, expected=None):
        if not isinstance(items, list) or not items:
            errors.append(f'{label}: at least one explicitly read citation is required')
            return
        roots = set()
        for item in items:
            try:
                path, start, end = item['path'], item['start'], item['end']
                if type(start) is not int or type(end) is not int or not 1 <= start <= end:
                    raise ValueError('invalid line interval')
                canonical = reader.path(path).relative_to(reader.root).as_posix()
                lines, digest = reader.lines(path)
                if end > len(lines):
                    raise ValueError('line exceeds file length')
                ranges = reader.reads.get(canonical, [])
                if not all(any(a <= n <= b and sha == digest for a, b, sha in ranges)
                           for n in range(start, end + 1)):
                    raise ValueError('citation not explicitly read, or input changed')
                roots.add(canonical.split('/')[0])
            except (ValueError, KeyError, TypeError, OSError, UnicodeError) as exc:
                errors.append(f'{label}: invalid citation: {exc}')
        if expected and not expected <= roots:
            errors.append(f'{label}: evidence required from {sorted(expected)}')

    coverage = report.get('coverage')
    if not isinstance(coverage, dict):
        errors.append('coverage must describe all three libraries')
    else:
        for library in sorted(LIBRARIES):
            entry = coverage.get(library, {})
            if not isinstance(entry, dict):
                errors.append(f'coverage.{library}: object required')
                continue
            for field in ['mapped_areas', 'unread_areas', 'configuration_unknowns']:
                text(entry.get(field), f'coverage.{library}.{field}')

    modules, ids = report.get('modules'), {}
    if not isinstance(modules, list) or not modules:
        errors.append('modules must be a nonempty list')
        modules = []
    for module in modules:
        if not isinstance(module, dict):
            errors.append('module must be an object')
            continue
        ident, library = module.get('id'), module.get('library')
        if not isinstance(ident, str) or not re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,79}', ident):
            errors.append('module id must be a short safe identifier')
            continue
        if ident in ids:
            errors.append(f'duplicate module id: {ident}')
        ids[ident] = module
        if library not in LIBRARIES:
            errors.append(f'{ident}: unknown library')
        text(module.get('title'), f'{ident}.title')
        if module.get('depth') not in ['brief', 'detailed']:
            errors.append(f'{ident}: depth must be brief or detailed')
        sections = module.get('sections', {})
        for section in SECTIONS:
            text(sections.get(section) if isinstance(sections, dict) else None, f'{ident}.{section}')
        evidence(module.get('evidence'), ident, {library} if library in LIBRARIES else None)
    if {m.get('library') for m in ids.values()} != LIBRARIES:
        errors.append('module overview must include all three libraries')

    comparisons, comparison_ids = report.get('comparisons'), set()
    if not isinstance(comparisons, list):
        errors.append('comparisons must be a list (empty allowed with no recommendation)')
        comparisons = []
    for comparison in comparisons:
        if not isinstance(comparison, dict):
            errors.append('comparison must be an object')
            continue
        cid = comparison.get('id')
        if not isinstance(cid, str) or not re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,79}', cid) or cid in comparison_ids:
            errors.append('comparison id must be unique and safe')
        comparison_ids.add(str(cid))
        target, reference = ids.get(comparison.get('target')), ids.get(comparison.get('reference'))
        if not target or target['library'] != 'openssl' or not reference or reference['library'] not in LIBRARIES - {'openssl'}:
            errors.append(f'{cid}: comparison must link a target and a reference module')
        if comparison.get('relation') not in ['candidate', 'none', 'unknown']:
            errors.append(f'{cid}: relation must be candidate, none, or unknown')
        for field in ['basis', 'differences', 'unknowns']:
            text(comparison.get(field), f'{cid}.{field}')
        evidence(comparison.get('evidence'), str(cid), {'openssl', reference['library']} if reference else None)

    rec = report.get('recommendation')
    if not isinstance(rec, dict):
        errors.append('recommendation must be an object')
        return errors
    for field in ['rationale', 'scope', 'dependencies', 'reference_entries', 'blockers']:
        text(rec.get(field), f'recommendation.{field}')
    if rec.get('confidence') not in ['proposed', 'tentative', 'unable']:
        errors.append('recommendation.confidence must be proposed, tentative, or unable')
    chosen = rec.get('primary')
    if rec.get('confidence') == 'unable':
        if chosen is not None:
            errors.append('unable recommendation must have null primary')
    elif chosen not in ids or ids[chosen]['library'] != 'openssl':
        errors.append('primary must identify an OpenSSL module')
    elif ids[chosen].get('depth') != 'detailed':
        errors.append('primary module must have detailed reading')
    alternatives = rec.get('alternatives', [])
    if not isinstance(alternatives, list) or any(not isinstance(x, str) or x not in ids or ids[x]['library'] != 'openssl' or x == chosen for x in alternatives):
        errors.append('alternatives must name distinct target modules other than primary')
    links = rec.get('comparisons', [])
    if not isinstance(links, list) or any(not isinstance(x, str) or x not in comparison_ids for x in links):
        errors.append('recommendation links unknown comparisons')
    if chosen and not links:
        errors.append('primary requires a comparison record, including explicit none/unknown if needed')
    if chosen and isinstance(links, list) and not any(
            isinstance(c, dict) and c.get('id') in links and c.get('target') == chosen
            for c in comparisons):
        errors.append('primary must link a comparison about that same module')
    if isinstance(alternatives, list) and (len(alternatives) > 2 or
            (all(isinstance(item, str) for item in alternatives) and len(set(alternatives)) != len(alternatives))):
        errors.append('at most two distinct alternatives are allowed')
    return errors


def render(report, directory):
    modules_dir = directory / 'modules'
    modules_dir.mkdir()
    navigation = ['# 三库模块概览', '', '本报告由模型生成；结构检查不等于语义正确，须用户审核。', '']
    for library, details in report['coverage'].items():
        navigation += [f'## {library}', '', json.dumps(details, ensure_ascii=False, indent=2), '']
    for module in report['modules']:
        navigation.append(f"- [{module['title']}](modules/{module['id']}.md) · {module['library']} · {module['depth']}")
        lines = [f"# {module['title']}", '', f"库：{module['library']}；阅读深度：{module['depth']}", '']
        for section in SECTIONS:
            lines += [f'## {section}', '', module['sections'][section], '']
        lines += ['## 已读取证据', '']
        lines += [f"- `{e['path']}:{e['start']}-{e['end']}`" for e in module['evidence']]
        (modules_dir / f"{module['id']}.md").write_text('\n'.join(lines) + '\n', encoding='utf-8')
    (directory / 'overview.md').write_text('\n'.join(navigation) + '\n', encoding='utf-8')
    comparisons = ['# 跨库比较记录', '']
    for item in report['comparisons']:
        comparisons += [f"## {item['id']}", '',
                        f"[{item['target']}](modules/{item['target']}.md) ↔ [{item['reference']}](modules/{item['reference']}.md)", '',
                        f"对应状态：{item['relation']}", '']
        for field in ['basis', 'differences', 'unknowns']:
            comparisons += [f"**{field}：** {item[field]}", '']
        comparisons += [f"- `{e['path']}:{e['start']}-{e['end']}`" for e in item['evidence']] + ['']
    (directory / 'comparisons.md').write_text('\n'.join(comparisons), encoding='utf-8')
    rec = report['recommendation']
    lines = ['# 模块推荐（待用户审核）', '', f"建议状态：{rec['confidence']}；首选：{rec['primary']}", '']
    if rec['primary']:
        lines += [f"[首选模块说明](modules/{rec['primary']}.md)", '']
    lines += ['[跨库比较记录](comparisons.md)', '', f"备选：{', '.join(rec.get('alternatives', [])) or '无'}", '']
    for field in ['rationale', 'scope', 'dependencies', 'reference_entries', 'blockers']:
        lines += [f'## {field}', '', rec[field], '']
    (directory / 'recommendation.md').write_text('\n'.join(lines), encoding='utf-8')
    (directory / 'review.json').write_text(json.dumps({'status': 'pending_user_review',
        'selected_module': None, 'conditions': [], 'note': '无用户批准，不得进入阶段 2。'}, ensure_ascii=False, indent=2), encoding='utf-8')
