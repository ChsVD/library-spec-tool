"""Module-wide conservative dependency planning; never authorizes proof execution."""
import argparse
import json
import re
from collections import defaultdict
from pathlib import Path
from .inventory import mask_noncode
from .pipeline import load_manifest
from .prepare import load_contracts
from stage1.runner import snapshot


def plan(root, manifest, contracts=()):
    inventory = manifest.get('selection_inventory', {})
    selection = inventory.get('selection', {})
    if selection.get('kind') != 'module':
        raise ValueError('frontier requires a module-wide manifest, not a preselected function group')
    root = Path(root).resolve(strict=True)
    if manifest.get('expected_input_snapshot', snapshot(root)) != snapshot(root):
        raise ValueError('input differs from module plan')
    nodes = manifest['functions']
    by_symbol = defaultdict(list)
    for n in nodes:
        by_symbol[n['symbol']].append(n)
    macros = set()
    file_issues = {g.get('path') for g in inventory.get('gaps', [])}
    for f in inventory.get('files', []):
        if f['path'].endswith(('.c', '.h')) and f.get('sha256'):
            text = (root / f['path']).read_text()
            macros.update(re.findall(r'^\s*#\s*define\s+([A-Za-z_]\w*)', mask_noncode(text), re.M))
    rows = []
    for n in nodes:
        src = n['source']
        code = mask_noncode('\n'.join((root / src['path']).read_text().splitlines()[src['start']-1:src['end']]))
        body = code[code.index('{')+1:]
        calls = sorted(set(re.findall(r'\b([A-Za-z_]\w*)\s*\(', body)) - {'if', 'for', 'while', 'switch', 'sizeof', '_Alignof', 'return', '_Generic', 'int', 'long', 'short', 'char', 'unsigned', 'signed', 'void', 'float', 'double', '_Bool'})
        edges = []
        for symbol in calls:
            options = by_symbol.get(symbol, [])
            # A same-file definition may be static; cross-file names need linkage review.
            local = [x for x in options if x['source']['path'] == src['path']]
            candidates = local or options
            supplied = [c for c in contracts if c['symbol'] == symbol and c['configuration'] == selection['configuration']]
            state = ('macro_requires_expansion' if symbol in macros else
                     'ambiguous_definition' if len(candidates) > 1 else
                     'processed_interface' if len(supplied) == 1 else
                     'unprocessed_callee' if candidates else 'unresolved_external_or_indirect')
            edges.append({'symbol': symbol, 'candidate_ids': [x['id'] for x in candidates],
                          'state': state, 'interface': {k:v for k,v in supplied[0].items() if k!='text'} if state=='processed_interface' else None})
        uncertainty = []
        if n.get('preprocessor_context') or re.search(r'^\s*#', body, re.M):
            uncertainty.append('conditional source not preprocessed')
        if src['path'] in file_issues:
            uncertainty.append('source inventory has unresolved syntax')
        if re.search(r'\b(?:asm|__asm__|__asm)\b', body):
            uncertainty.append('inline assembly requires inspection')
        if re.search(r'(?:->|\.)\s*\w+\s*\(|\(\s*\*|\)\s*\(', body):
            uncertainty.append('possible indirect or non-simple call')
        blockers = [e for e in edges if e['state']!='processed_interface']
        rows.append({'id':n['id'],'symbol':n['symbol'],'source':src,'dependencies':edges,
                     'uncertainties':uncertainty,
                     'status':'blocked_dependencies' if blockers else 'needs_configuration_review' if uncertainty else 'candidate_for_review',
                     'unprocessed_dependency_count':len(blockers)})
    rows.sort(key=lambda r:(r['unprocessed_dependency_count'],len(r['uncertainties']),r['source']['path'],r['source']['start']))
    return {'status':'pending_user_review','selection':selection,'method':'conservative lexical index; no preprocessing or proof-readiness claim',
            'inventory_gaps':inventory.get('gaps',[]),'functions':rows,
            'recommended_ids':[r['id'] for r in rows if r['status']=='candidate_for_review'],
            'proof_ready_ids':[], 'note':'All module functions retained, including blocked and conditional variants. Recommendations require review; no automatic export to execution.'}


def save(result, output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    (output/'frontier.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    lines=['# 模块内函数候选与依赖','','仅供审核；不是证明就绪清单。按未处理依赖数排序，不自动选择单一文件。',
           '调用由保守词法扫描定位；宏、条件编译、间接调用和未解析源码仍需核查。','','| 函数 | 位置 | 状态 | 待处理依赖 |','|---|---|---|---|']
    for r in result['functions']:
        deps=', '.join(e['symbol']+': '+e['state'] for e in r['dependencies'] if e['state']!='processed_interface') or '无已识别的未处理调用'
        lines.append('| '+r['symbol']+' | '+r['source']['path']+':'+str(r['source']['start'])+' | '+r['status']+' | '+deps+' |')
    lines+=['','未解析范围数：'+str(len(result['inventory_gaps']))+'；这些缺口未被当作无依赖。','']
    (output/'FRONTIER.md').write_text('\n'.join(lines))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',default='input');p.add_argument('--manifest',required=True)
    p.add_argument('--output',required=True);p.add_argument('--callee-contracts')
    a=p.parse_args()
    try:
        if Path(a.output).resolve().is_relative_to(Path(a.input).resolve()):raise ValueError('output must be outside input')
        manifest,_=load_manifest(a.manifest,a.input)
        result=plan(a.input,manifest,load_contracts(a.callee_contracts) if a.callee_contracts else ())
        save(result,a.output)
        print(json.dumps({'status':result['status'],'functions':len(result['functions']),'recommendations':len(result['recommended_ids'])}))
    except (ValueError,OSError) as e:p.error(str(e))


if __name__=='__main__':main()
