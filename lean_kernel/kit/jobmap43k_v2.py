#!/usr/bin/env python3
"""Job map v2 (= v1's unit rule with a byte-class scan instead of the box walk, so C4 runs in minutes;
pure Python, no numpy).
usage: jobmap43k_v2.py DATA_DIR CASE NB TARGET_RECS OUT.tsv
Units = whole jobs inside one shard, in stream order; a unit closes before the job that would push it past TARGET_RECS,
so a job larger than TARGET_RECS is a unit by itself (v1's rule). One row per unit:
  case shard unit j0 njobs nrecs nbytes      (unit = index within the case; nbytes = the unit's job-stream bytes)
Stream grammar (lean/'s S43Core/Tree.lean, kit/walk43_v1.py): byte 33..33+NB-1 = split, 112..121 = leaf followed by two digit
bytes 48..111; the byte classes are disjoint, so a job is the shortest prefix with leaves = splits + 1 (and has 4 x leaves - 1
bytes). Checks: only those byte classes; every leaf byte has two digit bytes and every digit byte belongs to one; per shard
jobs found = ranges col 2, leaves = col 3, bytes = col 4, the last job ends at the last byte; skeleton: only split/'z'
bytes and its 'z' count = total jobs. (Box arithmetic is not replayed here: v1 and the kernel walk do that.)"""
import sys
d, case, nb, target, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
CLS = bytearray(b'X' * 256)
for b in range(33, 33 + nb): CLS[b] = ord('S')
for b in range(112, 122): CLS[b] = ord('L')
for b in range(48, 112): CLS[b] = ord('D')
CLS = bytes(CLS)
skel = open(d + '/s/skel.txt', 'rb').read()
SK = bytearray(b'X' * 256)
for b in range(33, 33 + nb): SK[b] = ord('S')
SK[122] = ord('z')
tsk = skel.translate(bytes(SK))
assert b'X' not in tsk, 'skeleton: bad byte'
rg = [tuple(int(x) for x in l.split()) for l in open(d + '/s/ranges.txt') if l.strip()]
assert tsk.count(b'z') == sum(r[1] for r in rg), ('skeleton jobs', tsk.count(b'z'), sum(r[1] for r in rg))
rows = []; unit = 0
for si, (j0, nj, nrec_expect, nbytes) in enumerate(rg):
    s = open(d + '/s/shard_%05d.txt' % si, 'rb').read()
    assert len(s) == nbytes, (si, len(s), nbytes)
    t = s.translate(CLS)
    assert b'X' not in t, (si, 'bad byte')
    t2 = t.replace(b'LDD', b'L')
    assert b'D' not in t2, (si, 'digit outside a leaf or leaf without two digits')
    assert t2.count(b'L') == nrec_expect, (si, t2.count(b'L'), nrec_expect)
    jrec = []; need = 1; lv = 0
    for ch in t2:
        if ch == 76:
            need -= 1; lv += 1
            if need == 0:
                jrec.append(lv); lv = 0; need = 1
        else:
            need += 1
    assert need == 1 and lv == 0, (si, 'stream ends inside a job')
    assert len(jrec) == nj, (si, len(jrec), nj)
    assert sum(4 * r - 1 for r in jrec) == nbytes
    cur = None
    for k, r in enumerate(jrec):
        if cur is not None and cur[2] + r > target:
            rows.append((case, si, unit) + tuple(cur)); unit += 1; cur = None
        if cur is None: cur = [j0 + k, 0, 0, 0]
        cur[1] += 1; cur[2] += r; cur[3] += 4 * r - 1
    rows.append((case, si, unit) + tuple(cur)); unit += 1
with open(out, 'w') as f:
    f.write('case\tshard\tunit\tj0\tnjobs\tnrecs\tnbytes\n')
    for r in rows: f.write('\t'.join(map(str, r)) + '\n')
print(case, 'shards', len(rg), 'jobs', tsk.count(b'z'), 'units', len(rows), 'records', sum(r[5] for r in rows),
      'max unit recs', max(r[5] for r in rows), 'bytes', sum(r[6] for r in rows))
