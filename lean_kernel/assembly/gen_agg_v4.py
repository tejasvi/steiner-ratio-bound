#!/usr/bin/env python3
"""gen_agg_v4.py (v4 = v2 --module + `lean --setup` JSONs): aggregator tree over the unit modules.

usage: python3 -I gen_agg_v4.py --map JOBMAP.tsv --out OUTDIR [--fanin 64] [options]
JOBMAP.tsv: one row per unit module in stream order: case, unit, module, startSt name, endSt name [, unit theorem name]
  (tab separated; lines starting with '#' or 'case' are skipped; the unit theorem defaults to <namespace of startSt>.unit).
Per case k, level 1 aggregators take F consecutive units, level 2 F consecutive level-1 aggregators, ... until one remains;
then Root. Each aggregator (plain, non-module file) imports its children and proves
    theorem agg : CHAIN(k, first child's start, last child's end)
from the children's facts by folding --trans, with one link lemma `l<j> : <end of child j-1> = <start of child j> := rfl`
per adjacent pair (the exposed stack literals make these rfl checks). Root proves CHAIN(k, ROOT(k), END) from the top
aggregator with `lstart : ROOT(k) = <first start> := rfl` and `lend : <last end> = END := rfl`.
Options:
  --chain-fmt   'S43K.ChainOK {k} {a} {b}'   the chain predicate (Python format; {k} case, {a}/{b} the stacks)
  --trans       'S43K.chainOK_trans'          CHAIN a b -> CHAIN b c -> CHAIN a c (implicit stacks)
  --of-unit     ''                            lemma turning a unit theorem into CHAIN (empty: the unit theorem is CHAIN)
  --lib-import  ''                            comma-separated modules every aggregator also imports (K3 glue)
  --root-fmt    'S43K.rootSt{k}'   --root-import ''   --end-fmt '[]'      (no --root-import: Root files are not emitted)
  --prefix      'S43KAgg'          --no-index-check   (negative controls only: keep a map with gaps/swaps)
  --module      module-form aggregators/roots: `public import` of the first and last child (their stacks appear in the
                statement), private `import` of the others, `public theorem agg`/`root`, private link lemmas
v4: always module form (v2 --module) and, per module, OUTDIR/setup/<module>.json for `lean --setup`, whose importArts
list every unit/aggregator the build will load (the children and, transitively, their public boundary children) by their
public .olean only, so the assembly box needs no .olean.server/.olean.private of any unit. Needs --unit-olean-root (and
--agg-build, default OUTDIR/build). No boundary literals needed.
Outputs: OUTDIR/src/<prefix>/C<k>/A<lvl>_<i:05d>.lean, .../Root.lean, OUTDIR/setup/*.json, OUTDIR/build_order.tsv (level, module),
OUTDIR/agg_map.tsv (module, case, level, children, first, last, start, end), OUTDIR/MANIFEST.sha256. Refuses an existing OUTDIR."""
import argparse, hashlib, os, sys

ap = argparse.ArgumentParser()
ap.add_argument('--map', required=True)
ap.add_argument('--out', required=True)
ap.add_argument('--fanin', type=int, default=64)
ap.add_argument('--chain-fmt', default='S43K.ChainOK {k} {a} {b}')
ap.add_argument('--trans', default='S43K.chainOK_trans')
ap.add_argument('--of-unit', default='')
ap.add_argument('--lib-import', default='')
ap.add_argument('--root-fmt', default='S43K.rootSt{k}')
ap.add_argument('--root-import', default='')
ap.add_argument('--end-fmt', default='[]')
ap.add_argument('--prefix', default='S43KAgg')
ap.add_argument('--no-index-check', action='store_true')
ap.add_argument('--unit-olean-root', required=True)
ap.add_argument('--agg-build', default='')
a = ap.parse_args()
a.module = True
import json
uroot = os.path.abspath(a.unit_olean_root)
abuild = os.path.abspath(a.agg_build or os.path.join(a.out, 'build'))
closure = {}   # module -> set of (module, kind) loaded with it (its public boundary children, transitively)
kind = {}
if a.fanin < 2:
    sys.exit('ERROR: fan-in must be >= 2')
if os.path.exists(a.out):
    sys.exit('ERROR: %s exists' % a.out)

rows = {}
for ln, line in enumerate(open(a.map), 1):
    line = line.rstrip('\n')
    if not line.strip() or line.startswith('#') or line.startswith('case'):
        continue
    f = line.split('\t')
    if len(f) not in (5, 6):
        sys.exit('ERROR: %s:%d: expected 5 or 6 tab-separated fields' % (a.map, ln))
    k, u, mod, st, en = int(f[0]), int(f[1]), f[2], f[3], f[4]
    thm = f[5] if len(f) == 6 else st.rsplit('.', 1)[0] + '.unit'
    rows.setdefault(k, []).append((u, mod, st, en, thm))
for k, us in rows.items():
    idx = [u for u, *_ in us]
    if not a.no_index_check and idx != list(range(idx[0], idx[0] + len(idx))):
        sys.exit('ERROR: case %d: unit indices are not consecutive in stream order (first %d, n %d)' % (k, idx[0], len(idx)))
    if len(set(m for _, m, *_ in us)) != len(us):
        sys.exit('ERROR: case %d: duplicate unit module' % k)

chain = lambda k, x, y: a.chain_fmt.format(k=k, a=x, b=y)
libs = [m for m in a.lib_import.split(',') if m]
written, order, amap = [], [], []

def setup_json(name, kids):
    need = set()
    for m in kids:
        need.add(m); need |= {x for x, _ in closure.get(m, set())}
    arts = {m: [[os.path.join(uroot if kind[m] == 'unit' else abuild, m.replace('.', '/') + '.olean')]] for m in sorted(need)}
    full = os.path.join(a.out, 'setup', name + '.json')
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, 'w') as fh:
        fh.write(json.dumps({'name': name, 'isModule': True, 'importArts': arts, 'dynlibs': [], 'plugins': [], 'options': {}}, indent=1) + '\n')
    written.append(full)

def emit(path, text):
    full = os.path.join(a.out, 'src', path)
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, 'w') as fh:
        fh.write(text)
    written.append(full)

def aggregate(k, lvl, i, kids):
    """kids: list of (module, fact, start, end); returns the new node"""
    name = '%s.C%d.A%d_%05d' % (a.prefix, k, lvl, i)
    if a.module:
        pub = {0, len(kids) - 1}
        L = ['module', ''] + [('public import %s' if j in pub else 'import %s') % m for j, (m, *_) in enumerate(kids)]
        L += ['public import %s' % m for m in libs]
    else:
        L = ['import %s' % m for m, *_ in kids] + ['import %s' % m for m in libs]
    L += ['', '/-! %s: case %d, level %d, %d children (gen_agg_v4.py) -/' % (name, k, lvl, len(kids)), '',
          'namespace %s' % name, '']
    for j in range(1, len(kids)):
        L.append('theorem l%d : %s = %s := rfl' % (j, kids[j - 1][3], kids[j][2]))
    s0 = kids[0][2]
    L += ['', '%stheorem agg : %s := by' % ('public ' if a.module else '', chain(k, s0, kids[-1][3]))]
    L.append('  have t0 : %s := %s' % (chain(k, s0, kids[0][3]), kids[0][1]))
    for j in range(1, len(kids)):
        L.append('  have t%d : %s := %s t%d (l%d ▸ %s)' % (j, chain(k, s0, kids[j][3]), a.trans, j - 1, j, kids[j][1]))
    L += ['  exact t%d' % (len(kids) - 1), '', 'end %s' % name, '']
    emit(name.replace('.', '/') + '.lean', '\n'.join(L))
    order.append((lvl, name))
    amap.append((name, k, lvl, len(kids), kids[0][0], kids[-1][0], s0, kids[-1][3]))
    kind[name] = 'agg'
    closure[name] = {(kids[0][0], kind[kids[0][0]]), (kids[-1][0], kind[kids[-1][0]])} | closure.get(kids[0][0], set()) | closure.get(kids[-1][0], set())
    setup_json(name, [m for m, *_ in kids])
    return (name, name + '.agg', s0, kids[-1][3])

for k in sorted(rows):
    nodes = []
    for u, mod, st, en, thm in rows[k]:
        fact = ('%s %s' % (a.of_unit, thm)) if a.of_unit else thm
        kind[mod] = 'unit'
        nodes.append((mod, '(%s)' % fact if a.of_unit else fact, st, en))
    lvl = 0
    while len(nodes) > 1 or lvl == 0:
        lvl += 1
        nodes = [aggregate(k, lvl, i // a.fanin, nodes[i:i + a.fanin]) for i in range(0, len(nodes), a.fanin)]
    top = nodes[0]
    if a.root_import:
        name = '%s.C%d.Root' % (a.prefix, k)
        r = a.root_fmt.format(k=k)
        if a.module:
            L = ['module', '', 'import %s' % top[0], 'public import %s' % a.root_import] + ['public import %s' % m for m in libs]
        else:
            L = ['import %s' % top[0], 'import %s' % a.root_import] + ['import %s' % m for m in libs]
        L += ['', '/-! %s: case %d from its top aggregator %s (gen_agg_v4.py) -/' % (name, k, top[0]), '',
              'namespace %s' % name, '',
              'theorem lstart : %s = %s := rfl' % (r, top[2]),
              'theorem lend : %s = %s := rfl' % (top[3], a.end_fmt), '',
              '%stheorem root : %s := by' % ('public ' if a.module else '', chain(k, r, a.end_fmt)),
              '  have t : %s := %s' % (chain(k, top[2], top[3]), top[1]),
              '  rw [lstart, ← lend]',
              '  exact t', '', 'end %s' % name, '']
        emit(name.replace('.', '/') + '.lean', '\n'.join(L))
        setup_json(name, [top[0]])
        order.append((lvl + 1, name))
        amap.append((name, k, lvl + 1, 1, top[0], top[0], r, a.end_fmt))

with open(os.path.join(a.out, 'build_order.tsv'), 'w') as fh:
    for lvl, name in sorted(order, key=lambda x: (x[0], x[1])):
        fh.write('%d\t%s\n' % (lvl, name))
with open(os.path.join(a.out, 'agg_map.tsv'), 'w') as fh:
    fh.write('module\tcase\tlevel\tchildren\tfirst\tlast\tstart\tend\n')
    for r in amap:
        fh.write('\t'.join(str(x) for x in r) + '\n')
with open(os.path.join(a.out, 'MANIFEST.sha256'), 'w') as fh:
    for p in sorted(written) + [os.path.join(a.out, 'build_order.tsv'), os.path.join(a.out, 'agg_map.tsv')]:
        fh.write('%s  %s\n' % (hashlib.sha256(open(p, 'rb').read()).hexdigest(), os.path.relpath(p, a.out)))
print('cases %s; units %d; aggregators %d; roots %d; levels per case %s; fan-in %d' % (
    sorted(rows), sum(len(v) for v in rows.values()), sum(1 for r in amap if not r[0].endswith('.Root')),
    sum(1 for r in amap if r[0].endswith('.Root')),
    {k: max(r[2] for r in amap if r[1] == k and not r[0].endswith('.Root')) for k in rows}, a.fanin))
