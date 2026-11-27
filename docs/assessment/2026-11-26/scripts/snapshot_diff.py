# Detect golden traces whose behaviour changes under snapshot reads of OTHER machines in phase 2.
# A phase-2 expression (set `to` string, emit payload string entries) of fired behaviour B reading
# A.x / A.state (A != B) reads a different value iff an earlier fired entry of the same step, of
# behaviour A, changed x (a `sets` record with before != after) or changed state (from != to).
import json, re, sys, glob, os
root = sys.argv[1]
REF = re.compile(r"(?<![\w'\"-])([A-Za-z_][\w]*(?:-[\w]+)*)\.([A-Za-z_][\w]*(?:-[\w]+)*)")
def strip_strings(s):
    return re.sub(r"'[^']*'|\"[^\"]*\"", "''", s)
def refs(src):
    return REF.findall(strip_strings(src))
def exprs_of_transition(t):
    out = []
    for e in t.get('effects', []):
        if 'set' in e and isinstance(e.get('to'), str): out.append(('set', e['set'], e['to']))
        if 'emit' in e:
            for k, v in (e.get('payload') or {}).items():
                if isinstance(v, str): out.append(('emit', e['emit'] + '.' + k, v))
    return out
stats = dict(inputs=0, steps=0, cross_static=set(), changed=[], nonint=set(), typed=set(), divmod=set(), strings=set())
for inp in sorted(glob.glob(os.path.join(root, '**', '*.input.json'), recursive=True)):
    name = os.path.relpath(inp, root).replace('.input.json', '')
    d = json.load(open(inp)); stats['inputs'] += 1
    tr = json.load(open(inp.replace('.input.json', '.trace.json')))
    beh = {b['id']: b for b in d.get('behaviors', [])}
    trans = {(b['id'], t['id']): t for b in d.get('behaviors', []) for t in b.get('transitions', [])}
    if any(b.get('types') for b in d.get('behaviors', [])): stats['typed'].add(name)
    txt = json.dumps(d)
    def walk(x):
        if isinstance(x, float) and x != int(x): stats['nonint'].add(name)
        if isinstance(x, dict): [walk(v) for v in x.values()]
        if isinstance(x, list): [walk(v) for v in x]
    walk(d)
    for (bid, tid), t in trans.items():
        for kind, tgt, src in exprs_of_transition(t) + ([('guard', '', t['guard'])] if t.get('guard') else []):
            s = strip_strings(src)
            if re.search(r"[^/]/[^/]|%", s): stats['divmod'].add(name)
            if "'" in src: stats['strings'].add(name)
            if kind == 'guard': continue
            for a, x in refs(src):
                if a in beh and a != bid: stats['cross_static'].add((name, bid, tid, kind, tgt, f"{a}.{x}"))
    for st in tr.get('steps', []):
        stats['steps'] += 1
        fired = st.get('fired', [])
        for j, f in enumerate(fired):
            t = trans.get((f['behavior'], f['transition']))
            if not t: continue
            for kind, tgt, src in exprs_of_transition(t):
                for a, x in refs(src):
                    if a not in beh or a == f['behavior']: continue
                    for g in fired[:j]:
                        if g['behavior'] != a: continue
                        if x == 'state' and g['from'] != g['to'] or any(s_['variable'] == x and s_['before'] != s_['after'] for s_ in g.get('sets', [])):
                            stats['changed'].append((name, st['index'], f['behavior'], f['transition'], f"{a}.{x}"))
print('inputs', stats['inputs'], 'steps', stats['steps'])
print('phase-2 cross reads (static):', len(stats['cross_static']))
for c in sorted(stats['cross_static']): print('  ', c)
print('steps whose phase-2 read changes under snapshot:', len(stats['changed']))
for c in stats['changed']: print('  ', c)
print('inputs with non-integer numbers:', sorted(stats['nonint']))
print('inputs with declared types:', len(stats['typed']), sorted(stats['typed'])[:10])
print('inputs with / or %:', sorted(stats['divmod']))
print('inputs with string literals in expressions:', len(stats['strings']))
