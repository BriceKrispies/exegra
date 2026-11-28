# Detect golden traces whose behaviour changes under snapshot reads of OTHER machines in phase 2
# (docs/assessment/2026-11-26/plan-M2.md, section 3; WG-5681 criterion 23).
#
# A phase-2 expression (a `set` whose `to` is a string, a string entry of an emit payload) of a fired
# instance reads another machine through `A.x` or `A.state` (A a behaviour other than its own), or reads
# every instance of a behaviour through an aggregate (`A.count.s`, `A.sum.x`, `A.min.x`, `A.max.x`,
# `A.instances.count`). Under snapshot reads it reads the start of the step; under today's rule it reads
# the configuration being written. The two can differ only in a step in which the reader and a machine
# it reads both fire. This script counts those steps (in either order of firing; a machine is a
# behaviour and an instance, `fired[].instance`), and among them the steps where the read machine
# fired earlier and changed what is read (a `sets` record with before != after, or from != to).
#
#   python snapshot_diff.py <goldens dir> [--check]
#
# With --check the exit status is 1 when any step has a reader and a machine it reads firing together.
import json, re, sys, glob, os

args = [a for a in sys.argv[1:] if not a.startswith('--')]
check = '--check' in sys.argv[1:]
root = args[0] if args else 'tests/conformance/goldens'
SEG = r"[A-Za-z_][\w]*(?:-[\w]+)*"
REF = re.compile(r"(?<![\w'\"-])(" + SEG + r")\.(" + SEG + r")(?:\.(" + SEG + r"))?")
AGG = {'count', 'sum', 'min', 'max', 'instances'}

def strip_strings(s):
    return re.sub(r"'[^']*'|\"[^\"]*\"", "''", s)

def refs(src):
    """(behaviour, what, aggregate) for every reference with a behaviour prefix."""
    out = []
    for a, x, y in REF.findall(strip_strings(src)):
        if y and x in AGG: out.append((a, y if x != 'instances' else 'count', True))
        else: out.append((a, x, False))
    return out

def exprs_of_transition(t):
    out = []
    for e in t.get('effects', []):
        if 'set' in e and isinstance(e.get('to'), str): out.append(('set', e['set'], e['to']))
        if 'emit' in e:
            for k, v in (e.get('payload') or {}).items():
                if isinstance(v, str): out.append(('emit', e['emit'] + '.' + k, v))
    return out

def changes(g, x):
    if x == 'state': return g.get('from') != g.get('to')
    return any(s_['variable'] == x and s_['before'] != s_['after'] for s_ in g.get('sets', []))

stats = dict(inputs=0, steps=0, cross_static=set(), together=[], changed=[])
for inp in sorted(glob.glob(os.path.join(root, '**', '*.input.json'), recursive=True)):
    name = os.path.relpath(inp, root).replace('.input.json', '').replace('\\', '/')
    tp = inp.replace('.input.json', '.trace.json')
    if not os.path.exists(tp): continue  # a golden the engine refuses has no trace
    d = json.load(open(inp, encoding='utf-8')); stats['inputs'] += 1
    tr = json.load(open(tp, encoding='utf-8'))
    beh = {b['id']: b for b in d.get('behaviors', [])}
    trans = {(b['id'], t['id']): t for b in d.get('behaviors', []) for t in b.get('transitions', [])}
    for (bid, tid), t in trans.items():
        for kind, tgt, src in exprs_of_transition(t):
            for a, x, agg in refs(src):
                if a in beh and (a != bid or agg): stats['cross_static'].add((name, bid, tid, kind, tgt, f"{a}.{x}", 'aggregate' if agg else 'machine'))
    for st in tr.get('steps', []):
        stats['steps'] += 1
        fired = st.get('fired', [])
        for j, f in enumerate(fired):
            t = trans.get((f['behavior'], f['transition']))
            if not t: continue
            me = (f['behavior'], f.get('instance'))
            for kind, tgt, src in exprs_of_transition(t):
                for a, x, agg in refs(src):
                    if a not in beh or (a == f['behavior'] and not agg): continue
                    for k, g in enumerate(fired):
                        if g['behavior'] != a or (g['behavior'], g.get('instance')) == me: continue
                        stats['together'].append((name, st['index'], f['behavior'], f.get('instance'), f['transition'], f"{a}.{x}", g.get('instance')))
                        if k < j and changes(g, x):
                            stats['changed'].append((name, st['index'], f['behavior'], f['transition'], f"{a}.{x}"))
print('inputs', stats['inputs'], 'steps', stats['steps'])
print('phase-2 reads of other machines and aggregates (static):', len(stats['cross_static']))
for c in sorted(stats['cross_static']): print('  ', c)
print('steps in which a reader and a machine it reads fire together:', len(stats['together']))
for c in stats['together']: print('  ', c)
print('steps whose phase-2 read changes under snapshot reads:', len(stats['changed']))
for c in stats['changed']: print('  ', c)
sys.exit(1 if check and stats['together'] else 0)
