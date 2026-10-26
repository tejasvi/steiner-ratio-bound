#!/usr/bin/env python3
"""Replay of lean/'s DFS code streams (S43Core/Tree.lean: walkTop/walkSkel/walk) in Python (untrusted
sampling/extraction tool). Boxes are mantissas at scale 2^-100 (hi None = +inf), exactly as lean/'s `halves`.
usage:
  walk43_v1.py skel  DATA_DIR NB                       -> number of job boxes (skelSize of lean/)
  walk43_v1.py check DATA_DIR NB CERT.bin N            -> compare the first N leaves of shard 0 with CERT records 0..N-1
  walk43_v1.py sample DATA_DIR NB EVERY SHARDS OUT.bin  -> every EVERY-th leaf of the listed shards (comma list or 'all'),
                                                          written in lean/'s ID64 record layout (id = global leaf index)"""
import sys, struct
P = 100
ONE = 1 << P

def halves(lo, hi, k):
    l = lo[k]; h = hi[k]
    if h is not None:
        if (l + h) % 2 != 0 or not l < h: raise ValueError('halves: not exact')
        m = (l + h) // 2
        hi1 = list(hi); hi1[k] = m
        lo2 = list(lo); lo2[k] = m
        return (lo, hi1), (lo2, hi)
    m = ONE if l == 0 else 2 * l
    hi1 = list(hi); hi1[k] = m
    lo2 = list(lo); lo2[k] = m
    return (lo, hi1), (lo2, hi)

def root_boxes(nb):
    """walkTop's fixed top levels: split variables nb-1, ..., 0 at 1 (lower half first), in walk order"""
    def rec(k, box):
        if k == 0: return [box]
        l, r = halves(box[0], box[1], k - 1)
        return rec(k - 1, l) + rec(k - 1, r)
    return rec(nb, ([0] * nb, [None] * nb))

def skel_boxes(skel, nb):
    out = []; pos = 0
    for rb in root_boxes(nb):
        stack = [rb]
        while stack:
            lo, hi = stack.pop()
            c = skel[pos]
            if 33 <= c < 33 + nb:
                l, r = halves(lo, hi, c - 33); stack.append(r); stack.append(l); pos += 1
            elif c == 122:
                out.append((lo, hi)); pos += 1
            else: raise ValueError('skel: bad code %d at %d' % (c, pos))
    assert pos == len(skel), (pos, len(skel))
    return out

def walk_job(s, pos, box, nb, emit):
    stack = [box]
    while stack:
        lo, hi = stack.pop()
        c = s[pos]
        if 33 <= c < 33 + nb:
            l, r = halves(lo, hi, c - 33); stack.append(r); stack.append(l); pos += 1
        elif 112 <= c <= 121:
            lid = -1 if c == 121 else c - 112
            d1, d2 = s[pos + 1], s[pos + 2]
            emit(lo, hi, (d1 - 48) * 64 + (d2 - 48), lid); pos += 3
        else: raise ValueError('job: bad code %d at %d' % (c, pos))
    return pos

def ranges(d):
    return [tuple(int(x) for x in l.split()) for l in open(d + '/s/ranges.txt') if l.strip()]

def rec_bytes(idx, lo, hi, sid, lid):
    b = struct.pack('<Q', idx)
    for l, h in zip(lo, hi):
        b += struct.pack('<dd', l / ONE, float('inf') if h is None else h / ONE)
    return b + struct.pack('<ii', sid, lid)

if __name__ == '__main__':
    mode, d, nb = sys.argv[1], sys.argv[2], int(sys.argv[3])
    skel = open(d + '/s/skel.txt', 'rb').read()
    jb = skel_boxes(skel, nb)
    if mode == 'skel':
        print('job boxes', len(jb)); sys.exit(0)
    rg = ranges(d)
    if mode == 'check':
        cert, n = sys.argv[4], int(sys.argv[5])
        rs = 8 + 16 * nb + 8
        f = open(cert, 'rb')
        s = open(d + '/s/shard_00000.txt', 'rb').read()
        got = []
        def emit(lo, hi, sid, lid):
            if len(got) < n: got.append((lo, hi, sid, lid))
        pos = 0; j0, njobs = rg[0][0], rg[0][1]
        for j in range(j0, j0 + njobs):
            pos = walk_job(s, pos, jb[j], nb, emit)
            if len(got) >= n: break
        bad = 0
        for i, (lo, hi, sid, lid) in enumerate(got):
            raw = f.read(rs)
            vals = struct.unpack('<' + 'd' * (2 * nb), raw[8:8 + 16 * nb]); s2, l2 = struct.unpack('<ii', raw[8 + 16 * nb:])
            lo2 = [round(vals[2 * k] * ONE) for k in range(nb)]
            hi2 = [None if vals[2 * k + 1] == float('inf') else round(vals[2 * k + 1] * ONE) for k in range(nb)]
            if (lo2, hi2, s2, l2) != (lo, hi, sid, lid): bad += 1
        print('compared', len(got), 'mismatches', bad); sys.exit(0)
    if mode == 'sample':
        every = int(sys.argv[4]); sh = sys.argv[5]; out = open(sys.argv[6], 'wb')
        shards = range(len(rg)) if sh == 'all' else [int(x) for x in sh.split(',')]
        cnt = [0, 0]
        for si in shards:
            s = open(d + '/s/shard_%05d.txt' % si, 'rb').read()
            j0, njobs = rg[si][0], rg[si][1]
            base = sum(r[2] for r in rg[:si])
            k = [0]
            def emit(lo, hi, sid, lid):
                if k[0] % every == 0:
                    out.write(rec_bytes(base + k[0], lo, hi, sid, lid)); cnt[1] += 1
                k[0] += 1
            pos = 0
            for j in range(j0, j0 + njobs):
                pos = walk_job(s, pos, jb[j], nb, emit)
            assert pos == len(s), (si, pos, len(s))
            assert k[0] == rg[si][2], (si, k[0], rg[si][2])
            cnt[0] += k[0]
        print('walked leaves', cnt[0], 'sampled', cnt[1])
