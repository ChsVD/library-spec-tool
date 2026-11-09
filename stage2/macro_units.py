"""Lexical macro ranges and unevaluated preprocessor branch ancestry."""
import re
from .inventory import mask_noncode


def scan(lines,path):
    masked=mask_noncode('\n'.join(lines)).splitlines()
    stack=[];units=[];i=0
    while i<len(lines):
        start=i;end=i
        while lines[end].endswith('\\'):
            end+=1
            if end>=len(lines):raise ValueError('unterminated preprocessor continuation')
        text=' '.join(masked[start:end+1])
        directive=re.match(r'^\s*#\s*(\w+)\b(.*)',text)
        if directive:
            kind,tail=directive.groups()
            source={'path':path,'start':start+1,'end':end+1}
            item={'source':source,'text':'\n'.join(lines[start:end+1])}
            if kind in ('if','ifdef','ifndef'):stack.append([item])
            elif kind in ('elif','else'):
                if not stack:raise ValueError('unmatched conditional branch')
                if re.match(r'^\s*#\s*else\b',stack[-1][-1]['text']):raise ValueError('branch after else')
                stack[-1].append(item)
            elif kind=='endif':
                if not stack:raise ValueError('unmatched endif')
                stack.pop()
            elif kind=='define':
                match=re.match(r'\s+([A-Za-z_]\w*)',tail)
                if match:units.append({'symbol':match.group(1),'source':source,
                    'conditions':[dict(x) for branch in stack for x in branch],
                    'condition_status':'unevaluated_branch_history'})
        i=end+1
    if stack:raise ValueError('unclosed conditional block')
    return units


def locate(lines,source,symbol):
    units=[u for u in scan(lines,source['path']) if u['symbol']==symbol
           and source['start']<=u['source']['start']<=source['end']]
    if not units:raise ValueError('macro definition not found in supplied interval')
    for unit in units:
        if unit['source']['end']>source['end']:
            raise ValueError('incomplete macro; read full definition '+str(unit['source']))
    return units
