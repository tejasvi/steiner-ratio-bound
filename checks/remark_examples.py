#!/usr/bin/env python3
"""remark_examples.py: exact checks of the two examples in Remark 3.9 of the paper.
Points are stored as (x, eta) with y = sqrt(3) * eta, so that chain points with edge directions at multiples of 60 degrees
have rational coordinates and rational squared distances (x^2 + 3 eta^2).
Exchange inequalities (Lemma 3.1) between points of a right-turning chain A_0 ... A_n: for p on sigma_i, q on sigma_j, i < j,
  |pq| >= |p A_i|,  |pq| >= |A_{j-1} q|,  |pq| >= a_k  (i < k < j),
checked exactly as quadratic polynomials in the edge parameters (t, r) in [0,1]^2 (minimum over corners, edge vertices and
the interior critical point).  usage: python3 -I -B remark_examples.py"""
from fractions import Fraction as Fr
import itertools

DIRS = [(Fr(1), Fr(0)), (Fr(1, 2), Fr(-1, 2)), (Fr(-1, 2), Fr(-1, 2)), (Fr(-1), Fr(0)), (Fr(-1, 2), Fr(1, 2)), (Fr(1, 2), Fr(1, 2))]
res = []


def report(name, ok):
    res.append(bool(ok))
    print(("OK   " if ok else "FAIL ") + name)


def chain(lengths):
    pts = [(Fr(0), Fr(0))]
    for k, a in enumerate(lengths):          # sigma_{k+1} has direction wbar^k (angle -60 k degrees)
        dx, de = DIRS[k % 6]
        x, e = pts[-1]
        pts.append((x + a * dx, e + a * de))
    return pts


def n2(p):
    return p[0] * p[0] + 3 * p[1] * p[1]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def quad_min(Q):
    """exact minimum over [0,1]^2 of Q(t,r) = q00 + q10 t + q01 r + q20 t^2 + q11 t r + q02 r^2 (dict of coefficients)."""
    def val(t, r):
        return Q[0, 0] + Q[1, 0] * t + Q[0, 1] * r + Q[2, 0] * t * t + Q[1, 1] * t * r + Q[0, 2] * r * r
    cands = [(t, r) for t in (Fr(0), Fr(1)) for r in (Fr(0), Fr(1))]
    for t in (Fr(0), Fr(1)):                 # edges t fixed: a r^2 + b r + c
        a = Q[0, 2]; bcoef = Q[0, 1] + Q[1, 1] * t
        if a != 0:
            r = -bcoef / (2 * a)
            if 0 < r < 1: cands.append((t, r))
    for r in (Fr(0), Fr(1)):
        a = Q[2, 0]; bcoef = Q[1, 0] + Q[1, 1] * r
        if a != 0:
            t = -bcoef / (2 * a)
            if 0 < t < 1: cands.append((t, r))
    det = 4 * Q[2, 0] * Q[0, 2] - Q[1, 1] ** 2
    if det != 0:                             # interior critical point
        t = (-2 * Q[0, 2] * Q[1, 0] + Q[1, 1] * Q[0, 1]) / det
        r = (-2 * Q[2, 0] * Q[0, 1] + Q[1, 1] * Q[1, 0]) / det
        if 0 < t < 1 and 0 < r < 1: cands.append((t, r))
    return min(val(t, r) for t, r in cands)


def exchange_ok(lengths):
    """True iff every exchange inequality between points of the chain holds (with the smallest margin)."""
    P = chain(lengths); n = len(lengths); worst = None
    for i, j in itertools.combinations(range(1, n + 1), 2):
        ai, aj = lengths[i - 1], lengths[j - 1]
        di, dj = DIRS[(i - 1) % 6], DIRS[(j - 1) % 6]
        # p = A_{i-1} + t ai di, q = A_{j-1} + r aj dj;  pq = q - p = C + r aj dj - t ai di
        C = sub(P[j - 1], P[i - 1])
        u = (-ai * di[0], -ai * di[1]); v = (aj * dj[0], aj * dj[1])
        def ip(p, q): return p[0] * q[0] + 3 * p[1] * q[1]
        base = {(0, 0): ip(C, C), (1, 0): 2 * ip(C, u), (0, 1): 2 * ip(C, v), (2, 0): ip(u, u), (1, 1): 2 * ip(u, v), (0, 2): ip(v, v)}
        rhs = [{(0, 0): ai * ai, (1, 0): -2 * ai * ai, (2, 0): ai * ai},          # |p A_i|^2 = ((1-t) ai)^2
               {(0, 2): aj * aj}]                                             # |A_{j-1} q|^2 = (r aj)^2
        rhs += [{(0, 0): lengths[k - 1] ** 2} for k in range(i + 1, j)]
        for R in rhs:
            Q = {key: base[key] - R.get(key, 0) for key in base}
            m = quad_min(Q)
            if worst is None or m < worst[0]: worst = (m, i, j)
    return worst[0] >= 0, worst


def foot(p, a, dvec):                        # foot of p on the line a + t dvec (dvec a unit direction in (x, eta) form)
    t = (p[0] - a[0]) * dvec[0] + 3 * (p[1] - a[1]) * dvec[1]
    return t, (a[0] + t * dvec[0], a[1] + t * dvec[1])


def cross(o, p, q):                          # orientation of (o, p, q), in units of sqrt(3)
    return (p[0] - o[0]) * (q[1] - o[1]) - (p[1] - o[1]) * (q[0] - o[0])


def segments_cross(p1, p2, q1, q2):          # proper crossing
    d1, d2 = cross(q1, q2, p1), cross(q1, q2, p2)
    d3, d4 = cross(p1, p2, q1), cross(p1, p2, q2)
    return d1 * d2 < 0 and d3 * d4 < 0


# (a) Remark 3.9(a): (u, t, v) = (0, 1, 4), edge lengths (1, 2, 1/5, 1/10, 1/20, 1/40)
La = [Fr(1), Fr(2), Fr(1, 5), Fr(1, 10), Fr(1, 20), Fr(1, 40)]
ok, worst = exchange_ok(La)
report(f"(a) all exchange inequalities between chain points hold (smallest margin {worst[0]} at sigma_{worst[1]}, sigma_{worst[2]})", ok)
P = chain(La)
tH, H = foot(P[0], P[4], DIRS[4])
report(f"(a) H lies on the ray from A4 through A5 (parameter {tH} > 0)", tH > 0)
report(f"(a) |A0 H|^2 = {n2(sub(H, P[0]))} < a1^2 = 1", n2(sub(H, P[0])) < 1)
report("(a) the side [A4, H] crosses sigma_1 = [A0, A1]", segments_cross(P[4], H, P[0], P[1]))

# (b) Remark 3.9(b): (s, c, e, a5) = (1, 3/2, 3/2, 17/10)
s, c, e, a5 = Fr(1), Fr(3, 2), Fr(3, 2), Fr(17, 10)
Lb = [Fr(1), s, c, e, a5]
ok, worst = exchange_ok(Lb)
report(f"(b) all exchange inequalities between chain points up to A5 hold (smallest margin {worst[0]})", ok)
P = chain(Lb)
W = (1 - c - e, Fr(0))
report(f"(b) e < s + 1 ({e} < {s + 1})", e < s + 1)
# ray from A5 in the direction of sigma_6 (wbar^5 = angle 60 degrees) meets the real axis at M
d6 = DIRS[5]
t = -P[5][1] / d6[1]
M = (P[5][0] + t * d6[0], Fr(0))
report(f"(b) M = {M[0]} lies on [W, A] = [{W[0]}, 0]", W[0] <= M[0] <= 0)
report(f"(b) |AM|^2 = {n2(M)} = (6/5)^2", n2(M) == Fr(36, 25))
report(f"(b) |A5 M|^2 = {n2(sub(M, P[5]))} = (4/5)^2", n2(sub(M, P[5])) == Fr(16, 25))
report(f"(b) |AM| < a5", n2(M) < a5 * a5)
print(f"SUMMARY: {sum(res)} OK, {len(res) - sum(res)} FAIL")
