"""Function identities, call-site requirements and bounded graph projections."""
import copy
import hashlib
import json
from stage1.contracts import safe_id


def digest(value):
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True).encode()).hexdigest()


def validate_manifest(manifest):
    if manifest.get('version') != 1 or not isinstance(manifest.get('scope_decision'), str) or not manifest['scope_decision'].strip():
        raise ValueError('version=1 and explicit scope_decision required')
    nodes = manifest.get('functions')
    if not isinstance(nodes, list) or not nodes:
        raise ValueError('functions must be a nonempty scoped list')
    ids = set()
    for node in nodes:
        ident = node.get('id')
        if not safe_id(ident) or ident in ids:
            raise ValueError('function IDs must be unique safe IDs')
        ids.add(ident)
        if not all(isinstance(node.get(k), str) and node[k].strip() for k in ('symbol', 'configuration')):
            raise ValueError('symbol and configuration required')
        source = node.get('source', {})
        if (not isinstance(source.get('path'), str) or type(source.get('start')) is not int
                or type(source.get('end')) is not int or not 1 <= source['start'] <= source['end']):
            raise ValueError('source interval required')
        if not isinstance(node.get('materials'), list) or any(x not in manifest.get('materials', {}) for x in node['materials']):
            raise ValueError('materials must name supplied material IDs')
    return manifest


def new_graph(manifest):
    return {'version': 1, 'coverage': 'selected functions only; incoming callers may be incomplete',
            'nodes': {n['id']: {**copy.deepcopy(n), 'selected': True, 'status': 'pending',
                'revision': 0, 'spec': None, 'review': None} for n in manifest['functions']},
            'edges': {}, 'discoveries': {},
            **({'selection_inventory':copy.deepcopy(manifest['selection_inventory'])} if 'selection_inventory' in manifest else {})}


def merge_discovery(graph, report):
    """Transactional merge: never silently unify conflicting source/config identities."""
    candidate = copy.deepcopy(graph)
    for node in report['neighbors']:
        old = candidate['nodes'].get(node['id'])
        if old and any(old[k] != node[k] for k in ('symbol', 'configuration', 'source')):
            raise ValueError('Conflicting function identity: ' + node['id'])
        if not old:
            candidate['nodes'][node['id']] = {**node, 'selected': False, 'status': 'context_only',
                                            'revision': 0, 'spec': None, 'review': None}
    for edge in report['edges']:
        old = candidate['edges'].get(edge['id'])
        if old and any(old[k] != edge[k] for k in ('caller', 'callee', 'callsite', 'condition', 'certainty')):
            raise ValueError('Conflicting call edge: ' + edge['id'])
        candidate['edges'][edge['id']] = {**edge, 'requirements': old.get('requirements', []) if old else []}
    candidate['discoveries'][report['function_id']] = report
    graph.clear()
    graph.update(candidate)


def layers(graph):
    """SCC condensation in caller-before-callee order (iterative, no recursion limit)."""
    selected = {k for k, v in graph['nodes'].items() if v['selected']}
    adj = {k: set() for k in selected}
    rev = {k: set() for k in selected}
    for e in graph['edges'].values():
        a, b = e['caller'], e['callee']
        if a in selected and b in selected:
            adj[a].add(b); rev[b].add(a)
    seen, order = set(), []
    for root in sorted(selected):
        stack = [(root, False)]
        while stack:
            node, done = stack.pop()
            if done:
                order.append(node); continue
            if node in seen: continue
            seen.add(node); stack.append((node, True))
            stack.extend((x, False) for x in sorted(adj[node], reverse=True) if x not in seen)
    groups, owners = [], {}
    for root in reversed(order):
        if root in owners: continue
        group, stack = [], [root]
        while stack:
            node = stack.pop()
            if node in owners: continue
            owners[node] = len(groups); group.append(node)
            stack.extend(rev[node] - owners.keys())
        groups.append(sorted(group))
    predecessors = {i: set() for i in range(len(groups))}
    for a in adj:
        for b in adj[a]:
            if owners[a] != owners[b]: predecessors[owners[b]].add(owners[a])
    result, remaining, done = [], set(predecessors), set()
    while remaining:
        ready = sorted(i for i in remaining if predecessors[i] <= done)
        result.append([groups[i] for i in ready]); done.update(ready); remaining.difference_update(ready)
    return result


def context(graph, ident, max_chars=18000):
    """Only one-hop cards, no transitive function bodies or full graph injection."""
    node = graph['nodes'][ident]
    edges = [copy.deepcopy(e) for e in graph['edges'].values() if ident in (e['caller'], e['callee'])]
    neighbors = {x for e in edges for x in (e['caller'], e['callee']) if x and x != ident}
    cards = []
    for key in sorted(neighbors):
        n = graph['nodes'][key]
        cards.append({k: n[k] for k in ('id', 'symbol', 'source', 'configuration', 'status', 'revision')})
    value = {'function': {k: node[k] for k in ('id', 'symbol', 'source', 'configuration')},
             'neighbors': cards, 'edges': edges,
             'incoming_edge_ids': [e['id'] for e in edges if e['callee']==ident],
             'outgoing_edge_ids': [e['id'] for e in edges if e['caller']==ident],
             'coverage': graph['discoveries'].get(ident, {}).get('coverage', {}),
             'unknowns': graph['discoveries'].get(ident, {}).get('unknowns', []),
             'warning': 'Call requirements are requests, NOT guarantees; neighbor specs remain unproved candidates.'}
    if len(json.dumps(value, ensure_ascii=False)) > max_chars:
        raise ValueError('local_context_limit: split scope or call-site analysis; no silent truncation')
    return value


def install_spec(graph, ident, spec, review):
    node = graph['nodes'][ident]
    node['revision'] += 1
    node.update(spec=copy.deepcopy(spec), review=copy.deepcopy(review),
                status='reviewed_candidate' if review['verdict']=='pass' else review['verdict'])
    for e in graph['edges'].values():
        if e['caller'] == ident:
            e['requirements'] = [{**r, 'caller_revision': node['revision']}
                for r in spec['call_requirements'] if r['edge_id'] == e['id']]
    # An updated neighbor invalidates previously reviewed assumptions in either direction.
    for e in graph['edges'].values():
        if ident not in (e['caller'], e['callee']): continue
        other = e['callee'] if e['caller']==ident else e['caller']
        if other and other != ident and graph['nodes'][other]['status']=='reviewed_candidate':
            graph['nodes'][other]['status'] = 'needs_recheck'
