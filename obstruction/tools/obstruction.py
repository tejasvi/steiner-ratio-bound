#!/usr/bin/env python3
"""obstruction.py: certified pointwise obstruction for the split/lemma family of Ke, Huang, Shu, He, Gai, Wang
(arXiv:2601.22365), d_regular local configuration, subcase f >= d with f := d, at exact rational points; python-flint arb balls.

Way 1, the published family: the 158 published d_regular splits x 9 lemma ids, with the published lemma formulas (indep43.py, a
transcription of their verify_certificate.jl and lemma_{0..8}.jl). A lemma condition counts as usable unless it is CERTAINLY false
(all comparisons are evaluated in "possibly true" semantics), so a pair whose condition is undecided is kept. L(S+) is the exact
Steiner minimal tree length for 2 and 3 points (Fermat-Torricelli; when the 120-degree case is undecided, the union of the candidate
cases) and the lemma's closed form for 4 points. For every usable pair it certifies F(w, rho0) = rho0 L(T*) + L(S+) - L(S-) > 0 and
encloses the critical rho_k = (L(S-) - L(S+)) / L(T*); it prints the maximum and the pair attaining it.

Way 3, all splittings (enum43's enumeration of Definition 13 splittings: lemma set l, V* = nonempty subset of {A, B, D}, S- = the
tree edges at V* plus any further tree edges, S+ = at most 4 configuration nodes outside V* that reconnect the remaining terminals
together with the R- and Q-subtrees), with certified one-sided bounds:
  - L(T*) from below: the cheapest forest linking each V* point to the outside (a known terminal outside V*, or a trapped point X / Y
    at the published lemma bound when the lemma condition is possibly true), computed as an exact minimum spanning tree on the lower
    endpoints of the edge-cost balls (V* plus one contracted outside vertex);
  - L(S+) from below: 2 points: the distance; 3 points: Fermat-Torricelli (exact case when the 120-degree test is decided, else the
    smaller candidate); 4 points: the minimum over the three pairings {ij|kl} of a certified lower bound of
    N_ij|kl = min over x, y of |xi| + |xj| + |xy| + |yk| + |yl| (every tree on four terminals, with at most two Steiner points, is such a
    network for some pairing, degenerate positions included), by a convex-duality certificate: vectors u1..u5 of norm <= 1 with
    u1 + u2 + u3 = 0 and u4 + u5 = u3 give N >= -<u1,i> - <u2,j> - <u4,k> - <u5,l> for all x, y (|z| >= <u,z>); the vectors come from a
    double-precision Weiszfeld optimum, the balance is made exact and the norms are bounded in arb (all vectors divided by the largest
    norm if it exceeds 1); for each pairing the best of the 8 ways to restore the balance is used; the result is also compared with
    (a) the Ptolemy/Simpson bound max |E_ij E_kl| over the equilateral apexes and (b) the largest 3-point bound, and the largest of
    the three valid bounds is kept;
  - L(S-) exact (edge (A,s) has length 1, the others are the case variables, f := d);
  -> a certified upper bound of every combination's critical rho = (L(S-) - L(S+)) / L(T*), and of the maximum over combinations.
usage: python3 -I -B obstruction.py OUTDIR      (needs python-flint; writes way1_<point>.txt and way3_<point>.txt)"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flint
from flint import arb, fmpq
import indep43 as I

flint.ctx.prec = 128
FAM = I.Family("d_regular")
TOOLS = os.path.dirname(os.path.abspath(__file__))
POINTS = {   # (b, c, d, s, e) as exact rationals; f := d
    "wstar": ((13656, 10000), (110927, 100000), (365604, 1000000), (1, 1), (171605, 1000000)),
    "w1": ((134514, 100000), (107421, 100000), (347656, 1000000), (100391, 100000), (167969, 1000000)),
}
RHO0 = {"wstar": (856, 1000), "w1": (8572, 10000)}
ZERO = arb(0)


def ex(nd): return arb(fmpq(*nd))


# --- condition semantics: certain (as in the checker) or possible (kept unless certainly false)
CERTAIN = (I.lt, I.le, I.ge)
def possibly(on):
    if on:
        I.lt = lambda a, b: not bool(a >= b)
        I.le = lambda a, b: not bool(a > b)
        I.ge = lambda a, b: not bool(a < b)
    else:
        I.lt, I.le, I.ge = CERTAIN


def cond(fn, P, g, fval):
    """(possibly true, certainly true) of a lemma condition"""
    possibly(True)
    try: p = bool(fn(P, g, fval))
    finally: possibly(False)
    return p, bool(fn(P, g, fval))


def angle_status(a, b, c):
    """angle ABC: (possibly >= 120, possibly < 120)"""
    u, v = I.psub(a, b), I.psub(c, b)
    d = I.dot(u, v); q = I.FOUR * d * d; r = I.norm2(u) * I.norm2(v)
    cert_lt = bool(d >= 0) or bool(q < r)
    cert_ge = bool(d < 0) and bool(q >= r)
    return (not cert_lt), (not cert_ge)


def smt3_cases(a, b, c):
    """enclosures of the Fermat-Torricelli cases that are possible: list of balls; the exact SMT length is one of them"""
    pts = (a, b, c); out = []; all_lt = True
    for i in range(3):
        p, q, r = pts[i], pts[(i + 1) % 3], pts[(i + 2) % 3]
        pge, plt = angle_status(q, p, r)
        if pge: out.append(I.dist(p, q) + I.dist(p, r))
        if not plt: all_lt = False
    if all_lt:
        S = abs(I.cross(I.psub(b, a), I.psub(c, a))) / I.TWO
        out.append(I.sqrt_nn((I.norm2(I.psub(a, b)) + I.norm2(I.psub(b, c)) + I.norm2(I.psub(c, a))) / I.TWO + I.TWO * I.SQ3 * S))
    return out


def union(balls):
    lo = min((x.lower() for x in balls), key=lambda t: float(t.mid()))
    hi = max((x.upper() for x in balls), key=lambda t: float(t.mid()))
    for x in balls:      # exact endpoint comparisons (lower()/upper() are exact)
        if bool(x.lower() < lo): lo = x.lower()
        if bool(x.upper() > hi): hi = x.upper()
    return lo.union(hi)


def setup(name):
    V = [ex(x) for x in POINTS[name]] + [None]
    V[FAM.vid["f"]] = V[FAM.vid["d"]]
    return V, FAM.coords(V), dict(zip(FAM.vars, V))


# ------------------------------------------------------------------ way 1
NONLINEAR = ("st_cond3", "st_cond7")   # the only lemma conditions that are not linear in (b, c, d, s, e); all others are linear


def way1(name, out, mode="possible"):
    """mode: 'possible' (conditions kept unless certainly false), 'lin' (the two nonlinear 4-point conditions ignored, i.e. treated
    as true), 'none' (all lemma conditions ignored; informative only)"""
    V, P, g = setup(name)
    def cnd(fn):
        if mode == "none" or (mode == "lin" and fn.__name__ in NONLINEAR): return True, True
        return cond(fn, P, g, 2)
    rho0 = ex(RHO0[name])
    splits = I.read_splits(FAM, os.path.join(TOOLS, "splits", "d_regular_splits.txt"))
    names = FAM.nodes; imp = (FAM.nid["X"], FAM.nid["Y"])
    rows = []; n_pairs = n_poss = n_cert = 0; bad = []
    for k, sp in enumerate(splits):
        for lid in range(9):
            n_pairs += 1
            lem = FAM.lemmas[lid]; ok_p = ok_c = True; t = ZERO
            for (a, b) in sp.T_star:
                if a in imp or b in imp:
                    cf = lem.get((a, b))
                    if cf is None: ok_p = ok_c = False; break
                    p, c = cnd(cf[0]); ok_p &= p; ok_c &= c
                    if not ok_p: break
                    t += cf[1](P, g)
                else:
                    t += I.dist(P[names[a]], P[names[b]])
            if not ok_p: continue
            sm = ZERO
            for idx in sp.S_minus: sm += I.ONE if idx == 0 else V[idx - 1]
            kk = len(sp.S_plus)
            if kk <= 1: spl = ZERO
            elif kk == 2: spl = I.dist(P[names[sp.S_plus[0]]], P[names[sp.S_plus[1]]])
            elif kk == 3: spl = union(smt3_cases(*(P[names[i]] for i in sp.S_plus)))
            else:
                cf = lem.get(sp.S_plus)
                if cf is None: continue
                p, c = cnd(cf[0]); ok_p &= p; ok_c &= c
                if not ok_p: continue
                spl = cf[1](P, g)
            n_poss += 1; n_cert += ok_c
            F0 = rho0 * t + spl - sm
            if not bool(t > 0): bad.append((k + 1, lid, "L(T*) not certainly > 0")); continue
            rk = (sm - spl) / t
            if not bool(F0 > 0): bad.append((k + 1, lid, "F(rho0) not certainly > 0"))
            rows.append((rk, k + 1, lid, ok_c, F0))
    rows.sort(key=lambda r: -float(r[0].upper().mid()))
    tag = {"possible": "", "lin": "_linear_conditions_only", "none": "_no_conditions"}[mode]
    with open(os.path.join(out, f"way1{tag}_{name}.txt"), "w") as fo:
        pr = lambda *a: print(*a, file=fo)
        pr({"possible": "", "lin": "NONLINEAR CONDITIONS st_cond3, st_cond7 IGNORED (treated as true; the linear ones kept). ", "none": "ALL LEMMA CONDITIONS IGNORED (informative). "}[mode] + f"way 1 (published family) at {name} = (b,c,d,s,e) = {[f'{n}/{d}' for n, d in POINTS[name]]}, f := d; rho0 = {RHO0[name][0]}/{RHO0[name][1]}")
        pr(f"pairs evaluated {n_pairs} (158 splits x 9 lemma ids); usable (condition not certainly false) {n_poss}; of these with the condition certainly true {n_cert}")
        top = rows[0]
        pr(f"max critical rho over usable pairs: in [{top[0].lower().str(12, radius=False)}, {top[0].upper().str(12, radius=False)}] at split {top[1]} (1-based line of d_regular_splits.txt), lemma {top[2]}")
        pr("top 10 pairs (critical rho enclosure, split, lemma, condition certainly true):")
        for rk, k, lid, okc, F0 in rows[:10]:
            pr(f"  [{rk.lower().str(12, radius=False)}, {rk.upper().str(12, radius=False)}]  split {k}  lemma {lid}  {okc}")
        pr(f"pairs without a certified F(w, rho0) > 0: {len(bad)} {bad[:5]}")
        pr("RESULT: " + ("OBSTRUCTION CERTIFIED: every usable pair has F(w, rho0) > 0, so no box containing w can be certified at rho0 by this family"
                         if not bad else "NOT CERTIFIED"))
    return rows[0], bad


# ------------------------------------------------------------------ way 3
NODES = ["A", "B", "s", "r", "D", "P", "Q", "R"]
EDGES = [("A", "s"), ("B", "s"), ("s", "r"), ("r", "D"), ("r", "P"), ("P", "Q"), ("P", "R")]
KNOWN = ["A", "B", "D"]


def smt_lower(pts):
    k = len(pts)
    if k <= 1: return ZERO
    if k == 2: return I.dist(*pts).lower()
    if k == 3:
        return min((x.lower() for x in smt3_cases(*pts)), key=lambda t: float(t.mid()))   # refined below by exact compare
    best3 = None
    for tri in itertools.combinations(pts, 3):
        v = smt_lower(list(tri))
        if best3 is None or bool(v > best3): best3 = v
    pair = None
    for (i, j), (kk, l) in (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))):
        a, b, c, d = pts[i], pts[j], pts[kk], pts[l]
        Es = [I.padd(a, rot(I.psub(b, a), sg)) for sg in (1, -1)]
        Fs = [I.padd(c, rot(I.psub(d, c), sg)) for sg in (1, -1)]
        m = None
        for E in Es:
            for Fp in Fs:
                v = I.dist(E, Fp).lower()
                if m is None or bool(v > m): m = v
        v = dual_lb(a, b, c, d)
        if v is not None and bool(v > m): m = v
        if pair is None or bool(m < pair): pair = m
    return pair if bool(pair > best3) else best3


def fl(p): return (float(p[0].mid()), float(p[1].mid()))


def weiszfeld_pair(a, b, c, d, iters=6000):
    import math
    def wz(pts, x):
        num = [0.0, 0.0]; den = 0.0
        for q in pts:
            r = math.hypot(q[0] - x[0], q[1] - x[1])
            if r < 1e-15: return q
            num[0] += q[0] / r; num[1] += q[1] / r; den += 1 / r
        return (num[0] / den, num[1] / den)
    x = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2); y = ((c[0] + d[0]) / 2, (c[1] + d[1]) / 2)
    for _ in range(iters):
        x = wz([a, b, y], x); y = wz([c, d, x], y)
    return x, y


def dual_lb(a, b, c, d):
    """certified lower bound of min_{x,y} |xa| + |xb| + |xy| + |yc| + |yd| (convex duality), or None"""
    import math
    af, bf, cf, df = fl(a), fl(b), fl(c), fl(d)
    x, y = weiszfeld_pair(af, bf, cf, df)
    def unit(p, q):
        r = math.hypot(p[0] - q[0], p[1] - q[1])
        return (0.0, 0.0) if r < 1e-300 else ((p[0] - q[0]) / r, (p[1] - q[1]) / r)
    num = {1: unit(x, af), 2: unit(x, bf), 3: unit(x, y), 4: unit(y, cf), 5: unit(y, df)}
    A = lambda t: (arb(t[0]), arb(t[1]))
    best = None
    for dx, dy in ((3, 4), (3, 5), (1, 3), (2, 3), (1, 4), (1, 5), (2, 4), (2, 5)):
        u = {k: A(v) for k, v in num.items()}
        if dx == 3:
            u[3] = (-(u[1][0] + u[2][0]), -(u[1][1] + u[2][1]))
            o = 5 if dy == 4 else 4
            u[dy] = (u[3][0] - u[o][0], u[3][1] - u[o][1])
        elif dy == 3:
            u[3] = (u[4][0] + u[5][0], u[4][1] + u[5][1])
            o = 2 if dx == 1 else 1
            u[dx] = (-(u[o][0] + u[3][0]), -(u[o][1] + u[3][1]))
        else:
            o = 2 if dx == 1 else 1
            u[dx] = (-(u[o][0] + u[3][0]), -(u[o][1] + u[3][1]))
            o = 5 if dy == 4 else 4
            u[dy] = (u[3][0] - u[o][0], u[3][1] - u[o][1])
        lam = I.ONE
        for k in range(1, 6):
            nk = I.sqrt_nn(I.norm2(u[k])).upper()
            if bool(nk > lam): lam = nk
        val = -(I.dot(u[1], a) + I.dot(u[2], b) + I.dot(u[4], c) + I.dot(u[5], d))
        v = (val / lam).lower()
        if best is None or bool(v > best): best = v
    return best


def rot(u, sg):
    c, s = I.ONE / I.TWO, sg * I.SQ3 / I.TWO
    return (c * u[0] - s * u[1], s * u[0] + c * u[1])


def exact_min(xs):
    m = xs[0]
    for x in xs[1:]:
        if bool(x < m): m = x
    return m


def connected(edges, need):
    par = {x: x for x in NODES}
    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for a, b in edges: par[f(a)] = f(b)
    return len({f(x) for x in need}) == 1


def way3(name, out):
    V, Pc, g = setup(name)
    P = {k: Pc[k] for k in NODES}
    elen = {("A", "s"): I.ONE, ("B", "s"): g["b"], ("s", "r"): g["s"], ("r", "D"): g["d"], ("r", "P"): g["c"], ("P", "Q"): g["f"], ("P", "R"): g["e"]}
    Dlo = lambda p, q: I.dist(P[p], P[q]).lower()
    cache = {}
    def splo(S):
        key = tuple(sorted(S))
        if key not in cache:
            v = smt_lower([P[x] for x in key])
            if len(key) == 3: v = exact_min([x.lower() for x in smt3_cases(*[P[x] for x in key])])
            cache[key] = v
        return cache[key]
    bounds = []
    for l in range(9):
        bl = {}
        for key, (cf, fn) in FAM.lemmas[l].items():
            if len(key) != 2: continue
            na, nb = FAM.nodes[key[0]], FAM.nodes[key[1]]
            p, c = cond(cf, Pc, g, 2)
            if not p: continue
            v = fn(Pc, g).lower()
            if nb in ("X", "Y"): bl[(na, nb)] = v
            elif na in ("X", "Y"): bl[(nb, na)] = v
        bounds.append(bl)
    ncombo = 0; best = None; nlt = 0
    for l in range(9):
        for r in range(1, 4):
            for Vs in itertools.combinations(KNOWN, r):
                outside = [x for x in KNOWN if x not in Vs]
                w = {}
                for x in Vs:
                    cands = [Dlo(x, y) for y in outside] + [bounds[l][(x, t)] for t in ("X", "Y") if (x, t) in bounds[l]]
                    w[x] = exact_min(cands) if cands else None
                verts = list(Vs); intree = set(); LT = ZERO; finite = True
                # Prim from the contracted outside vertex SUPER (a V* point without a direct link reaches it through other V* points)
                key = {x: w[x] for x in verts}       # None = no edge yet (+infinity)
                while len(intree) < len(verts):
                    x = None
                    for y in verts:
                        if y in intree or key[y] is None: continue
                        if x is None or bool(key[y] < key[x]): x = y
                    if x is None: finite = False; break
                    intree.add(x); LT = LT + key[x]
                    for y in verts:
                        if y not in intree:
                            dxy = Dlo(x, y)
                            if key[y] is None or bool(dxy < key[y]): key[y] = dxy
                if not finite or not bool(LT > 0): continue
                inc = [e for e in EDGES if e[0] in Vs or e[1] in Vs]
                rest = [e for e in EDGES if e not in inc]
                for kk in range(len(rest) + 1):
                    for extra in itertools.combinations(rest, kk):
                        Sm = inc + list(extra)
                        LSm = ZERO
                        for e in Sm: LSm = LSm + elen[e]
                        rem = [e for e in EDGES if e not in Sm]
                        need = outside + ["R", "Q"]
                        cand = [x for x in NODES if x not in Vs]
                        for m in range(0, 5):
                            for Sp in itertools.combinations(cand, m):
                                joins = rem + [(Sp[0], q) for q in Sp[1:]] if len(Sp) > 1 else rem
                                if not connected(joins, need): continue
                                ncombo += 1
                                num = LSm - splo(Sp)
                                if not bool(num > 0): nlt += 1; continue
                                ru = (num / LT).upper()
                                if best is None or bool(ru > best[0]): best = (ru, l, Vs, tuple(Sm), Sp)
    with open(os.path.join(out, f"way3_{name}.txt"), "w") as fo:
        pr = lambda *a: print(*a, file=fo)
        pr(f"way 3 (all Definition-13 splittings, enum43 enumeration) at {name} = (b,c,d,s,e) = {[f'{n}/{d}' for n, d in POINTS[name]]}, f := d")
        pr(f"combinations enumerated {ncombo} (lemma set x V* x S- x S+, connectivity test passed, finite T*); with L(S-) - L(S+)_lower <= 0: {nlt}")
        pr(f"certified upper bound of the maximum critical rho over all combinations: {best[0].str(15, radius=False)}")
        pr(f"  attained (as an upper bound) at lemma set {best[1]}, V* {best[2]}, S- {best[3]}, S+ {best[4]}")
    return best, ncombo


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else "."
    for name in POINTS:
        t, bad = way1(name, out)
        for mode in ("lin", "none"):
            t2, bad2 = way1(name, out, mode=mode)
            print(name, "way1 mode", mode, "max", t2[0].upper().str(10, radius=False), "split", t2[1], "lemma", t2[2], "uncertified", len(bad2))
        b, n = way3(name, out)
        print(name, "way1 max", t[0].upper().str(10, radius=False), "split", t[1], "lemma", t[2], "uncertified", len(bad), "| way3 bound", b[0].str(10, radius=False), "combos", n)
