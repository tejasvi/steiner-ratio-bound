#!/usr/bin/env python3
"""Unit generator. Writes the unit modules of the selected units of one shard or, with --natbin OUT.bin, the units'
records in lean/'s ID64 layout for the native pre-run (natk): id = the leaf's index in the case (job map
order), box ends as exact doubles (scale 2^-100 / 2^100, +inf; a box end is an exact double iff its odd part has <= 53
bits), split id (0 for skip leaves, as in the units) and lemma id (-1 = skip, natk maps it to 9).
The case's walk starts from the full box [⟨[0]*nb, [none]*nb⟩] with lean/'s fixed top splits (walkTop:
variables nb-1 .. 0 at 1.0, lower half first) as explicit split codes, interleaved in DFS pre-order with lean/'s
skeleton; --units A-B selects consecutive units of one shard (direct stream offsets from the job map's nbytes);
--selfcheck replays S43Walk.WalkK2 (unpack + walkFold + unitWalkOK) in Python on every written unit's packed codes and
literals.
Untrusted data generator: the kernel checks everything it writes.
usage: gen43k_shard_v4.py DATA_DIR CASE SHARD JOBMAP.tsv OUTROOT [--units A-B] [--selfcheck] [--walk-only] [--natbin OUT.bin]
  DATA_DIR = the case's data dir from lean/'s data archives (s/skel.txt, s/ranges.txt, s/shard_<SHARD:05d>.txt); CASE in C1..C4; JOBMAP = the case's frozen
  job map (kit/jobmap43k_v2.py: case shard unit j0 njobs nrecs nbytes). Default: every unit of the shard.
Writes OUTROOT/S43U/<CASE>/S<shard:04d>/U<unit:06d>.lean (module S43U.<CASE>.S<shard>.U<unit>, namespace = module name) and
OUTROOT/jobs.tsv, one row per written unit: name deps est_gb est_s lean_file olean_file src_sha256 nrecs ncodes (the first six
columns are the build nodes' job format; paths relative to OUTROOT). Module text: the unit's merged
code stream (per job: skeleton codes since the previous 'z' incl. top splits, its 'z', its subtree codes) packed 32 seven-bit
codes per Nat, exposed public literals startSt/endSt (the skeleton stack before/after, BoxS at scale 2^-40), the records (reverse
order), `theorem walk : unitWalkOK ... = true`, one `checkRecordK ... ≠ .fail` theorem per record, `allOK`, and the one public
theorem `unit : UnitClaim st fval nb startSt endSt`. Unit i's endSt = unit i+1's startSt; unit 0's startSt = [full box]; the last
unit's endSt = [] (asserted when written).
Checks: the shard's job map rows are contiguous and add up to ranges cols 2-4; each written unit's records and stream bytes equal
its row; lean/'s skeleton splits into exactly 2^nb root subtrees; with --selfcheck the replay reproduces endSt and the records."""
import sys, hashlib, os, struct
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import walk43_v1 as W
CASES = {'C1': (False, 3, 6), 'C2': (True, 2, 7), 'C3': (False, 1, 6), 'C4': (True, 1, 8)}   # lean/'s S43Data/C*/Case.lean
EST_S = {'C1': 0.161, 'C2': 0.345, 'C3': 0.141, 'C4': 0.359}   # full-load seconds per record (measured), for the cost estimate only
d, case, shard, jm, outroot = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
st, fval, nb = CASES[case]
walk_only = '--walk-only' in sys.argv; selfcheck = '--selfcheck' in sys.argv
rows = []; recbase = {}; acc_r = 0
for l in open(jm):
    f = l.rstrip('\n').split('\t')
    if f[0] != case: continue
    recbase[int(f[2])] = acc_r; acc_r += int(f[5])
    if int(f[1]) == shard: rows.append(tuple(int(x) for x in f[2:7]))
natbin = sys.argv[sys.argv.index('--natbin') + 1] if '--natbin' in sys.argv else None
nbf = open(natbin, 'wb') if natbin else None
rg = W.ranges(d)
j0s, njs, nrs, nbs = rg[shard]
assert rows and rows[0][1] == j0s, 'job map: first job'
for a, b in zip(rows, rows[1:]): assert a[1] + a[2] == b[1] and a[0] + 1 == b[0], 'job map: not contiguous'
assert sum(r[2] for r in rows) == njs and sum(r[3] for r in rows) == nrs and sum(r[4] for r in rows) == nbs, 'job map: totals'
offs = []; o = 0
for r in rows: offs.append(o); o += r[4]
if '--units' in sys.argv:
    ua, ub = (int(x) for x in sys.argv[sys.argv.index('--units') + 1].split('-'))
    sel = [i for i, r in enumerate(rows) if ua <= r[0] <= ub]
    assert sel and rows[sel[0]][0] == ua and rows[sel[-1]][0] == ub, 'units not in this shard'
else:
    sel = list(range(len(rows)))
srows = [rows[i] for i in sel]
jfirst, jlast = srows[0][1], srows[-1][1] + srows[-1][2]          # jobs [jfirst, jlast)
ncase_jobs = sum(r[1] for r in rg)
starts = {r[1]: r[0] for r in srows}; ends = {r[1] + r[2] - 1: r[0] for r in srows}
def exact(x):     # x / 2^100 is an exact IEEE double: odd part <= 53 bits (magnitudes here are far inside the exponent range)
    return x == 0 or (x >> ((x & -x).bit_length() - 1)).bit_length() <= 53
def d60(x):
    assert x % (1 << 60) == 0, 'box end finer than 2^-40'
    return x >> 60
# full skeleton: top tree (depth nb) in pre-order, lean/'s root subtree i at top leaf i
skel = open(d + '/s/skel.txt', 'rb').read()
segs = []; pos = 0
for i in range(2 ** nb):
    need = 1; s0 = pos
    while need:
        c = skel[pos]; pos += 1
        if 33 <= c < 33 + nb: need += 1
        elif c == 122: need -= 1
        else: raise ValueError('skel code')
    segs.append(skel[s0:pos])
assert pos == len(skel), 'skeleton: not exactly 2^nb root subtrees'
full = bytearray()
def top(k, idx):
    if k == 0:
        full.extend(segs[idx]); return idx + 1
    full.append(33 + k - 1)
    return top(k - 1, top(k - 1, idx))
assert top(nb, 0) == 2 ** nb
FULLBOX = ([0] * nb, [None] * nb)
# skeleton pass up to the selection's last job: per job (prefix since the previous 'z' + 'z', box); stacks at unit borders
stack = [FULLBOX]; pos = 0; job = 0; prefix = []
start_st = {}; end_st = {}; per_job = {}
if 0 in starts: start_st[starts[0]] = list(stack)
while job < jlast:
    c = full[pos]; pos += 1
    lo, hi = stack.pop()
    if 33 <= c < 33 + nb:
        l, r = W.halves(lo, hi, c - 33); stack.append(r); stack.append(l); prefix.append(c)
    elif c == 122:
        if job >= jfirst: per_job[job] = (bytes(prefix + [c]), (lo, hi))
        prefix = []
        if job in ends: end_st[ends[job]] = list(stack)
        job += 1
        if job in starts: start_st[starts[job]] = list(stack)
    else: raise ValueError('skel code')
if jlast == ncase_jobs:
    assert pos == len(full) and stack == [], 'last unit: skeleton not used up / stack not empty'
def pack(bs):
    ws = []
    for i in range(0, len(bs), 32):
        v = 0
        for jj, b in enumerate(bs[i:i + 32]): v |= b << (7 * jj)
        ws.append(v)
    return ws
def onat(h): return 'none' if h is None else 'some %d' % d60(h)
def boxlit(b): return '⟨[%s], [%s]⟩' % (', '.join(str(d60(x)) for x in b[0]), ', '.join(onat(h) for h in b[1]))
def stacklit(stk): return '[' + ', '.join(boxlit(b) for b in reversed(stk)) + ']'
# --- Python replay of S43Walk.WalkK2 at scale 2^-40 (selfcheck): boxes as (tuple lo, tuple hi), stacks top-first
def b40(b): return (tuple(d60(x) for x in b[0]), tuple(None if h is None else d60(h) for h in b[1]))
def midW(l, h):
    if h is not None: return (l + h) // 2 if (l < h and (l + h) % 2 == 0) else None
    return 1099511627776 if l == 0 else 2 * l
def halfLo(b, k, m): hi = list(b[1]); hi[k] = m; return (b[0], tuple(hi))
def halfHi(b, k, m): lo = list(b[0]); lo[k] = m; return (tuple(lo), b[1])
def replay(ws, n, sk, recs_expect):
    codes = []
    for w in ws:
        for _ in range(32): codes.append(w & 127); w >>= 7
    codes = codes[:n]; sk = list(sk); js = []; acc = []; i = 0
    while i < len(codes):
        c = codes[i]; i += 1
        if not js:
            if not sk: return 'empty stacks'
            b = sk.pop(0)
            if c == 122: js = [b]; continue
            if 33 <= c < 33 + nb:
                m = midW(b[0][c - 33], b[1][c - 33])
                if m is None: return 'midW'
                sk = [halfLo(b, c - 33, m), halfHi(b, c - 33, m)] + sk; continue
            return 'skel code %d' % c
        b = js.pop(0)
        if 33 <= c < 33 + nb:
            m = midW(b[0][c - 33], b[1][c - 33])
            if m is None: return 'midW'
            js = [halfLo(b, c - 33, m), halfHi(b, c - 33, m)] + js; continue
        if 112 <= c <= 121:
            if i + 2 > len(codes): return 'leaf digits'
            d1, d2 = codes[i], codes[i + 1]; i += 2
            if not (48 <= d1 <= 111 and 48 <= d2 <= 111): return 'digit'
            acc.append((b[0], b[1], (d1 - 48) * 64 + (d2 - 48), 9 if c == 121 else c - 112)); continue
        return 'job code %d' % c
    if js: return 'job stack not empty'
    if list(reversed(acc)) != list(reversed(recs_expect)): return 'records differ'
    return sk
S = 'true' if st else 'false'
s = open(d + '/s/shard_%05d.txt' % shard, 'rb').read()
assert len(s) == nbs
out_rows = []
for k, (u, j0, nj, nr, nby) in zip(sel, srows):
    p = offs[k]; p_u = p; codes = b''; recs = []
    for j in range(j0, j0 + nj):
        pre, box = per_job[j]
        q = W.walk_job(s, p, box, nb, lambda lo, hi, sid, lid: recs.append((lo, hi, sid if lid >= 0 else 0, lid if lid >= 0 else 9)))
        codes += pre + s[p:q]; p = q
    assert len(recs) == nr and p - p_u == nby, ('unit', u, len(recs), nr, p - p_u, nby)
    if j0 + nj == ncase_jobs: assert end_st[u] == [], 'last unit: endSt not empty'
    ws = pack(codes)
    if selfcheck:
        sk0 = [b40(b) for b in reversed(start_st[u])]; sk1 = [b40(b) for b in reversed(end_st[u])]
        r40 = [(tuple(d60(x) for x in lo), tuple(None if h is None else d60(h) for h in hi), sid, lid) for lo, hi, sid, lid in recs]
        res = replay(ws, len(codes), sk0, r40)
        assert res == sk1, ('selfcheck', u, res if isinstance(res, str) else 'end stack differs')
    if nbf is not None:
        for i, (lo, hi, sid, lid) in enumerate(recs):
            b = struct.pack('<Q', recbase[u] + i)
            for l_, h_ in zip(lo, hi):
                lv = l_ / (1 << 100); hv = float('inf') if h_ is None else h_ / (1 << 100)
                assert exact(l_), 'lo not exact'
                assert h_ is None or exact(h_), 'hi not exact'
                b += struct.pack('<dd', lv, hv)
            nbf.write(b + struct.pack('<ii', sid, lid if lid != 9 else -1))
        out_rows.append(('N.' + '%s.S%04d.U%06d' % (case, shard, u), str(len(recs))))
        continue
    name = 'S43U.%s.S%04d.U%06d' % (case, shard, u)
    rel = 'S43U/%s/S%04d/U%06d' % (case, shard, u)
    L = ['module', '', 'public import S43Walk.WalkK2', 'set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '',
         '/-! %s: case %s jobs %d..%d (shard %d), %d records, %d codes; kit/gen43k_shard_v4.py (untrusted data) -/' % (
             name, case, j0, j0 + nj - 1, shard, len(recs), len(codes)),
         'namespace %s' % name,
         'def codes : List Nat := [' + ', '.join(map(str, ws)) + ']',
         'def ncodes : Nat := %d' % len(codes),
         '@[expose] public def startSt : List S43K.BoxS := ' + stacklit(start_st[u]),
         '@[expose] public def endSt : List S43K.BoxS := ' + stacklit(end_st[u])]
    for i, (lo, hi, sid, lid) in enumerate(recs):
        L.append('def r%d : S43K.RecK := ⟨[%s], [%s], %d, %d⟩' % (i, ', '.join(str(d60(x)) for x in lo), ', '.join(onat(h) for h in hi), sid, lid))
    L.append('def recsRev : List S43K.RecK := [' + ', '.join('r%d' % i for i in reversed(range(len(recs)))) + ']')
    L.append('theorem walk : S43K.unitWalkOK %d codes ncodes startSt endSt recsRev = true := by decide +kernel' % nb)
    if not walk_only:
        for i in range(len(recs)):
            L.append('theorem t%d : S43K.checkRecordK %s %d %d ⟨S43K.up60 r%d.lo, S43K.up60o r%d.hi⟩ r%d.sid r%d.lid ≠ .fail := by decide +kernel' % (
                i, S, fval, nb, i, i, i, i))
        nest = 'trivial'
        for i in range(len(recs)):        # recsRev = [r_{n-1}, ..., r_0]: innermost is r_0
            nest = '⟨t%d, %s⟩' % (i, nest)
        L.append('theorem allOK : S43K.ForallR (S43K.recOK %s %d %d) recsRev := %s' % (S, fval, nb, nest))
        L.append('public theorem unit : S43K.UnitClaim %s %d %d startSt endSt := ⟨codes, ncodes, recsRev, walk, allOK⟩' % (S, fval, nb))
    L.append('end %s' % name)
    txt = ('\n'.join(L) + '\n').encode()
    os.makedirs(os.path.join(outroot, os.path.dirname(rel)), exist_ok=True)
    with open(os.path.join(outroot, rel + '.lean'), 'wb') as f: f.write(txt)
    est_gb = 0.5 + 0.001 * len(recs)
    est_s = 5 + EST_S[case] * len(recs) + 0.004 * len(codes)
    out_rows.append((name, '-', '%.2f' % est_gb, '%.0f' % est_s, rel + '.lean', rel + '.olean', hashlib.sha256(txt).hexdigest(), str(len(recs)), str(len(codes))))
if nbf is not None:
    nbf.close()
    print(case, 'shard', shard, 'natbin units', len(out_rows), 'records', sum(int(r[1]) for r in out_rows))
    sys.exit(0)
with open(os.path.join(outroot, 'jobs.tsv'), 'w') as f:
    for r in out_rows: f.write('\t'.join(r) + '\n')
print(case, 'shard', shard, 'units', len(rows), 'written', len(out_rows), 'records', sum(r[3] for r in srows), 'selfcheck' if selfcheck else '')
