"""Select paths from branch roots to a shared callee, keeping all direct callers."""
import copy
from collections import defaultdict
from stage3.reference import build_graph


def select(root, manifest, target, root_symbols, *, graph_backend="fm-agent", graph_compile_commands=None):
    graph=build_graph(root,manifest,graph_backend=graph_backend,compile_commands=graph_compile_commands)
    targets={i for i,n in graph['nodes'].items() if n['symbol']==target}
    if not targets:raise ValueError('target missing: '+target)
    adj=defaultdict(set);rev=defaultdict(set)
    for e in graph['edges'].values():adj[e['caller']].add(e['callee']);rev[e['callee']].add(e['caller'])
    def reach(roots,links):
        seen=set();todo=list(roots)
        while todo:
            i=todo.pop()
            if i in seen:continue
            seen.add(i);todo.extend(links[i])
        return seen
    ancestors=reach(targets,rev)
    roots={i for i,n in graph['nodes'].items() if n['symbol'] in root_symbols}
    missing=set(root_symbols)-{graph['nodes'][i]['symbol'] for i in roots}
    if missing:raise ValueError('missing branch roots: '+str(sorted(missing)))
    disconnected=roots-ancestors
    absent={symbol for symbol in root_symbols if not any(graph['nodes'][i]['symbol']==symbol for i in roots & ancestors)}
    if absent:raise ValueError('branch root has no identified path to target: '+str(sorted(absent)))
    roots &= ancestors
    keep=reach(roots,adj)&ancestors
    direct={i for t in targets for i in rev[t]}
    supplemental=direct-keep
    roots |= supplemental
    keep |= reach(supplemental,adj)&ancestors
    result=copy.deepcopy(manifest);result['functions']=[{k:v for k,v in n.items() if k not in ('code','selected','status','spec','fqn')} for i,n in graph['nodes'].items() if i in keep]
    result['scope_decision']='All specified branch paths to '+target+' plus uncovered direct callers; external siblings remain context gaps.'
    parent=result.get('selection_inventory',{})
    result['selection_inventory']={'selection':parent.get('selection',{}),'scope_status':'enumerated','expected_function_ids':[n['id'] for n in result['functions']],
        'gaps':[],'parent_inventory_gaps':parent.get('gaps',[]),'method':'explicit branch-to-target subset; does not claim whole module coverage'}
    result['branch_scope']={'target':target,'target_ids':sorted(targets),'root_ids':sorted(roots),'requested_roots':list(root_symbols),
        'disconnected_root_variants':sorted(disconnected),'supplemental_root_ids':sorted(supplemental),'direct_caller_ids':sorted(direct),
        'excluded_ancestor_ids':sorted(ancestors-keep),'note':'covers specified branches and all direct callers recognized by the selected backend; incomplete candidate graph, not all possible module ancestors'}
    return result
