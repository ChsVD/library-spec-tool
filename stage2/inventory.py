"""Conservative C definition inventory. No preprocessing or completeness claim for gaps."""
import copy
import hashlib
import re
from pathlib import Path
from stage1.reader import Reader
from stage1.contracts import safe_id


def mask_noncode(text):
    # Preserve positions/newlines so original source intervals remain exact.
    pattern = re.compile(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'', re.S)
    return pattern.sub(lambda m: ''.join('\n' if c=='\n' else ' ' for c in m.group()),text)


def scan_c(text, path):
    code=mask_noncode(text)
    conditions={}; stack=[]; cleaned=[]; continued=False
    for number,line in enumerate(code.splitlines(keepends=True),1):
        directive=re.match(r'\s*#\s*(\w+)\b(.*)',line)
        if directive:
            op,expr=directive.groups()
            if op in ('if','ifdef','ifndef'): stack.append(f'{number}: #{op}{expr.strip() and " "+expr.strip()}')
            elif op in ('else','elif') and stack: stack[-1]+=f' -> {number}: #{op} {expr.strip()}'
            elif op=='endif' and stack: stack.pop()
        conditions[number]=list(stack)
        if directive or continued:
            cleaned.append(''.join('\n' if c=='\n' else ' ' for c in line))
            continued=line.rstrip().endswith('\\')
        else: cleaned.append(line)
    code=''.join(cleaned); found=[]; gaps=[]; i=0; segment=0
    while i<len(code):
        ch=code[i]
        if ch==';':
            statement=code[segment:i].strip()
            macro=re.fullmatch(r'([A-Za-z_]\w*)\s*\(.*\)',statement,re.S)
            if macro and macro.group(1) not in ('_Static_assert','static_assert'):
                gaps.append({'path':path,'line':text.count('\n',0,segment)+1,
                             'reason':'standalone macro/implicit declaration may generate functions; requires inspection'})
            segment=i+1
        elif ch=='}':
            gaps.append({'path':path,'line':text.count('\n',0,i)+1,'reason':'unmatched top-level closing brace; preprocessor branches require inspection'})
            segment=i+1
        elif ch=='{':
            prefix=code[segment:i]; depth=1; end=i+1
            while end<len(code) and depth:
                depth+=(code[end]=='{')-(code[end]=='}');end+=1
            if depth:
                gaps.append({'path':path,'line':text.count('\n',0,i)+1,'reason':'unbalanced body; no guessed source end'})
                break
            # Function declarator must end in a balanced parameter list. Attributes,
            # macro-generated names and conditional alternative signatures are gaps.
            declarations=[]; parens=0
            for match in re.finditer(r'[A-Za-z_]\w*|[()]',prefix):
                token=match.group()
                if token=='(': parens+=1
                elif token==')': parens-=1
                elif parens==0 and re.match(r'\s*\(',prefix[match.end():]):
                    declarations.append(token)
            is_data=('=' in prefix or re.match(r'^\s*(?:typedef\s+)?(?:struct|union|enum)\b[^()]*$',prefix) is not None)
            if not is_data:
                if len(declarations)==1 and prefix.rstrip().endswith(')') and parens==0:
                    symbol=declarations[0]
                    if symbol in ('if','for','while','switch','__attribute__','__declspec','int','void','char','long','short','unsigned','signed') or not re.search(r'\S',prefix[:re.search(r'\b'+re.escape(symbol)+r'\s*\(',prefix).start()]):
                        declarations=[]
                    else:
                        start=segment+len(prefix)-len(prefix.lstrip())
                        line=text.count('\n',0,start)+1
                        found.append({'symbol':symbol,'code_offsets':{'start':start,'end':end},'source':{'path':path,'start':line,'end':text.count('\n',0,end-1)+1},
                                      'preprocessor_context':conditions.get(line,[])})
                else: declarations=[]
                if not declarations:
                    gaps.append({'path':path,'line':text.count('\n',0,i)+1,'reason':'unrecognized top-level body/signature; do not silently omit'})
            i=end;segment=end;continue
        i+=1
    if code[segment:].strip():
        gaps.append({'path':path,'line':text.count('\n',0,segment)+1,'reason':'unclassified trailing source; may contain macro-generated definitions'})
    return found,gaps


def validate_selection_manifest(value):
    if value.get('version')!=2 or not isinstance(value.get('scope_decision'),str) or not value['scope_decision'].strip():
        raise ValueError('selection manifest needs version=2 and scope_decision')
    s=value.get('selection',{})
    if s.get('kind') not in ('module','function_group') or not safe_id(s.get('id')) or not safe_id(s.get('module_id')):
        raise ValueError('selection kind=module/function_group and safe id/module_id required')
    if not isinstance(s.get('paths'),list) or not s['paths'] or any(not isinstance(x,str) for x in s['paths']):
        raise ValueError('selection.paths must enumerate module/group source roots, not a function whitelist')
    if not isinstance(s.get('configuration'),str) or not s['configuration'].strip():raise ValueError('configuration assumptions required')
    if not isinstance(s.get('materials'),list) or any(x not in value.get('materials',{}) for x in s['materials']):
        raise ValueError('selection material IDs must exist')
    if 'functions' in value:raise ValueError('v2 selection must not carry a hand-selected function whitelist')
    for e in s.get('exclude_files',[]):
        if not isinstance(e,dict) or not isinstance(e.get('path'),str) or not isinstance(e.get('reason'),str) or not e['reason'].strip():
            raise ValueError('file exclusion needs an exact path and explicit reason')
    return value


def expand_selection(root, manifest):
    """Enumerate every definition in selected source files, independent of call reachability."""
    validate_selection_manifest(manifest)
    root=Path(root).resolve(strict=True)
    reader=Reader(root,root.parent/'unused-inventory-log.jsonl')  # Only path/files/lines; never execute/write.
    selection=manifest['selection']; paths=set()
    for name in selection['paths']:
        p=reader.path(name)
        if p.is_dir(): paths.update(reader.files(p.relative_to(root).as_posix()))
        elif p.is_file():paths.add(p.relative_to(root).as_posix())
        else:raise ValueError('scope path must be a file or directory')
    exclusions={e['path']:e['reason'] for e in selection.get('exclude_files',[])}
    if len(exclusions)!=len(selection.get('exclude_files',[])) or not set(exclusions)<=paths:
        raise ValueError('duplicate exclusion or exclusion outside selected roots')
    functions=[]; files=[]; gaps=[]
    for name in sorted(paths):
        record={'path':name}
        if name in exclusions:
            files.append({**record,'status':'excluded','reason':exclusions[name]});continue
        suffix=Path(name).suffix.lower()
        if suffix not in ('.c','.h'):
            files.append({**record,'status':'not_c_source','reason':'not indexed as C; not a claim of no functions'})
            if suffix in ('.s','.asm','.pl','.inc','.cpp','.cc','.cxx','.hpp'):
                gaps.append({**record,'reason':'possible implementation outside supported C inventory; explicitly review/exclude or add a supported inventory'})
            continue
        try:
            reader.path(name) # symlink boundary check
            lines,sha=reader.lines(name)
            entries,issues=scan_c('\n'.join(lines)+'\n',name)
        except (ValueError,OSError,UnicodeError) as exc:
            gaps.append({**record,'reason':str(exc)});files.append({**record,'status':'unread'});continue
        ids=[]
        for entry in entries:
            identity=f"{name}:{entry['source']['start']}:{entry['symbol']}"
            slug=re.sub('[^a-z0-9_-]','-',entry['symbol'].lower())[:42]
            ident=slug+'-'+hashlib.sha256(identity.encode()).hexdigest()[:12]
            node={**entry,'id':ident,'module_id':selection['module_id'],'group_id':selection['id'],
                  'configuration':selection['configuration']+'；源码预处理位置（未求值）：'+(' | '.join(entry['preprocessor_context']) or '无外层条件指令'),
                  'materials':list(selection['materials'])}
            functions.append(node);ids.append(ident)
        gaps.extend(issues)
        files.append({**record,'status':'needs_inspection' if issues else 'indexed','sha256':sha,'function_ids':ids})
    if selection['kind']=='function_group' and len(functions)<2:
        gaps.append({'reason':'function_group must enumerate multiple functions; inspect scope instead of silently reverting to a one-function experiment'})
    expanded=copy.deepcopy(manifest);expanded['version']=1;expanded['functions']=functions
    expanded['selection_inventory']={'selection':copy.deepcopy(selection),'files':files,'gaps':gaps,
        'expected_function_ids':[n['id'] for n in functions],
        'scope_status':'needs_scope_review' if gaps or not functions else 'enumerated',
        'method':'conservative C lexical inventory; each body still requires model discovery/read; preprocessing not evaluated'}
    return expanded


def progress(graph):
    selected={k:n['status'] for k,n in graph['nodes'].items() if n['selected']}
    inventory=graph.get('selection_inventory')
    expected=inventory['expected_function_ids'] if inventory else list(selected)
    missing=sorted(set(expected)-set(selected))
    pending=[k for k in expected if selected.get(k)!='reviewed_candidate']
    return {'selection_kind':inventory['selection']['kind'] if inventory else 'legacy_function_list',
            'selection_id':inventory['selection']['id'] if inventory else None,
            'expected_count':len(expected),'reviewed_count':sum(selected.get(k)=='reviewed_candidate' for k in expected),
            'pending_function_ids':pending,'missing_function_ids':missing,
            'inventory_gaps':inventory['gaps'] if inventory else [],
            'all_selected_complete':bool(expected) and not pending and not missing and not (inventory and inventory['gaps'])}
