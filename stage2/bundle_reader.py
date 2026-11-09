"""Original-coordinate Reader backed exclusively by verified copied source bundles."""
import hashlib
from copy import deepcopy
import json
from pathlib import Path
from stage1.reader import Reader


def verify_bundle(folder, manifest):
    folder=Path(folder).resolve(strict=True)
    for name,expected in manifest['files'].items():
        if not isinstance(name,str) or Path(name).is_absolute() or '..' in Path(name).parts or '\\' in name:
            raise ValueError('invalid bundle file name')
        p=(folder/name).resolve(strict=True)
        if not p.is_relative_to(folder) or hashlib.sha256(p.read_bytes()).hexdigest()!=expected:
            raise ValueError('bundle changed or escapes its directory: '+name)


class BundleReader(Reader):
    """No access to original repository. Missing lines are errors, not empty code."""
    def __init__(self,root,log,*,bundles):
        self.root=Path(root).resolve(strict=True);self.log=Path(log);self.reads={}
        self.bundles=[(Path(p).resolve(strict=True),deepcopy(m)) for p,m in bundles]
        self.content={};self.hashes={}
        for folder,m in self.bundles:
            verify_bundle(folder,m)
            for entry in m['mappings']:
                origin=entry['original'];copy=entry['bundle'];name=origin['path']
                if Path(name).is_absolute() or '..' in Path(name).parts or '\\' in name:
                    raise ValueError('invalid original source path')
                if any(type(x.get(k)) is not int for x in (origin,copy) for k in ('start','end')):raise ValueError('integer source intervals required')
                if not 1<=origin['start']<=origin['end']<=1000000 or not 1<=copy['start']<=copy['end']<=1000000:raise ValueError('invalid source interval')
                if copy['path'] not in m['files']:raise ValueError('mapping must reference a verified bundle file')
                if copy.get('transformed') or entry.get('transformed'):raise ValueError('transformed mappings unsupported')
                lines=(folder/copy['path']).read_text(encoding='utf-8').splitlines()[copy['start']-1:copy['end']]
                if len(lines)!=origin['end']-origin['start']+1:raise ValueError('mapping is not exact source text')
                if name in self.hashes and self.hashes[name]!=entry['sha256']:raise ValueError('mixed source versions')
                self.hashes[name]=entry['sha256'];target=self.content.setdefault(name,{})
                for number,text in zip(range(origin['start'],origin['end']+1),lines):
                    if number in target and target[number]!=text:raise ValueError('conflicting copied source')
                    target[number]=text
    def path(self,name):
        if not isinstance(name,str) or name not in self.content:raise ValueError('not_extracted: request additional material from extraction subagent')
        return self.root/name
    def lines(self,name):
        self.path(name)
        for folder,manifest in self.bundles:verify_bundle(folder,manifest)
        content=self.content[name]
        return [content.get(i,'') for i in range(1,max(content)+1)],self.hashes[name]
    def files(self,directory):
        if not isinstance(directory,str) or '..' in Path(directory).parts or Path(directory).is_absolute():raise ValueError('invalid directory')
        return iter(sorted(n for n in self.content if directory in ('.','') or n==directory or n.startswith(directory.rstrip('/')+'/')))
    def execute(self,action):
        try:
            for folder,manifest in self.bundles:verify_bundle(folder,manifest)
            op=action.get('tool');name=action.get('path','.')
            if op=='read':
                start=self.integer(action,'start',1,1,1000000);count=self.integer(action,'count',120,1,200)
                lines,sha=self.lines(name);end=min(start+count-1,len(lines))
                if start>end or any(n not in self.content[name] for n in range(start,end+1)):
                    raise ValueError('not_extracted: range includes missing source; use exact manifest ranges or request extraction')
                if sum(len(lines[n-1]) for n in range(start,end+1))>24000:raise ValueError('read exceeds character limit; use smaller interval')
                self.reads.setdefault(name,[]).append((start,end,sha))
                result={'path':name,'start':start,'end':end,'lines':[{'line':n,'text':lines[n-1]} for n in range(start,end+1)],
                        'sha256':sha,'source':'reviewed_adapted_input_not_original' if any(m.get('source_kind')=='reviewed_preparation' for _,m in self.bundles) else 'verified_extracted_copy','truncated':end<len(lines),'next_start':end+1}
            elif op=='search':
                result=self.search(action)
                result['coverage']='extracted snippets only; absence is not absence from repository'
            elif op=='batch':
                result=self.batch(action)
            elif op=='list':
                names=list(self.files(name));offset=self.integer(action,'offset',0,0,1000000)
                result={'entries':[{'path':p,'kind':'extracted_source','ranges':self.ranges(p)} for p in names[offset:offset+100]],'truncated':len(names)>offset+100}
            else:raise ValueError('unsupported Reader action')
        except (ValueError,OSError,UnicodeError,KeyError) as exc:result={'error':str(exc)}
        with self.log.open('a',encoding='utf-8') as stream:stream.write(json.dumps({'action':action,'result':result},ensure_ascii=False)+'\n')
        return result
    def ranges(self,name):
        result=[]
        for n in sorted(self.content[name]):
            if result and result[-1][1]+1==n:result[-1][1]=n
            else:result.append([n,n])
        return result


def reader_factory(bundles):
    return lambda root,log:BundleReader(root,log,bundles=bundles)


def bundles_from_nodes(run,nodes,inventory):
    from .graph import digest
    run=Path(run).resolve(strict=True)
    versions={x['path']:x.get('sha256') for x in inventory}
    result=[]
    for node in nodes:
        record=node.get('source_bundle')
        if not record:raise ValueError('selected function missing source bundle')
        folder=(run/record['path']).resolve(strict=True)
        if not folder.is_relative_to(run):raise ValueError('source bundle escapes run')
        m=json.loads((folder/'manifest.json').read_text())
        if digest(m)!=record['manifest_digest']:raise ValueError('source bundle manifest changed')
        verify_bundle(folder,m)
        adapted=m.get('source_kind')=='reviewed_preparation'
        if adapted and any(x['original']['path']!='prepared/'+m['function_id']+'/'+x['bundle']['path'] or x['sha256']!=m['files'].get(x['bundle']['path']) for x in m['mappings']):
            raise ValueError('invalid reviewed source namespace/hash')
        if not adapted and any(versions.get(x['original']['path'])!=x['sha256'] for x in m['mappings']):
            raise ValueError('source bundle does not match original input snapshot')
        result.append((folder,m))
    return result
