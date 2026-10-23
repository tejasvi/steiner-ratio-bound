#!/usr/bin/env python3
"""indep43.py: independent check of the CERTIFICATE LAYER of the Steiner-ratio lower bound of Ke, Huang, Shu, He, Gai, Wang
(arXiv:2601.22365, ICML 2026), in the record format of their certificate/{d_regular,d_steiner}/ (github keyisi2006/Steiner-Ratio,
commit 8f19604, MIT). Transcribed from their verify_certificate.jl and lemmas/lemma_{0..8}.jl; python-flint arb at
128 bits; rho is an exact rational.

What a record asserts and what is checked here (per record: region id, box [lo_i, hi_i] for the n case variables, split id, lemma id):
- the split's function F = rho * L(T*) + L(S+) - L(S-) is <= 0 (certainly, in ball arithmetic) at every vertex of the box with finite
  coordinates (vertex semantics; the reduction to vertices is the paper's Theorem 6 under its axis-unimodality "Shape Constraint", a
  LEMMA-LAYER obligation that is not checked here), where
    L(S-) = sum of the S- edge lengths (edge (A,s) has length 1, the others are the case variables),
    L(S+) = |PQ| for 2 points, the 3-point Steiner minimal tree length (upper bound if some angle >= 120 deg is not excluded) for 3,
            and a lemma's closed-form length (its condition must hold) for 4,
    L(T*) = sum over T* edges of |uv|, or of a lemma's upper bound when the edge meets a trapped point X or Y (condition must hold);
- in subcase f >= d (n = 7 or 5) the split must be monotone in f and f := d; in f <= d (n = 8 or 6) |S+| <= 3 and records with
  f_lo > d_hi are outside the subcase; boxes with an infinite upper end need that variable in mono_vars and lemma 0;
- d_steiner: records with max(u_lo, v_lo) > max(b_hi, 1) are covered by relabelling (symmetry) and skipped, as in the original.
Optional (--fullbox): F is also evaluated over the whole box (bounded variables), with up to B bisections, which removes the
Shape-Constraint dependence for the records that close. Coverage of the case domain by the regions is checked by cover43.py.
usage: python3 -I -B indep43.py FAMILY SUBCASE SPLITS.txt CERT.bin RHO NPROC OUT.jsonl [--fullbox=B] [--limit=N] [--start=K]
       FAMILY = d_steiner | d_regular; SUBCASE = f_ge_d | f_le_d; RHO = rational, e.g. 431/500
"""
import sys, os, ast, json, struct, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))      # mono43.py lives next to this file (python -I drops the script dir)
from fractions import Fraction as Fr
import flint
from flint import arb, fmpq

flint.ctx.prec = 128
SQ3 = arb(3).sqrt()
ONE, TWO, THREE, FOUR = arb(1), arb(2), arb(3), arb(4)


def ex(q):
    q = Fr(q)
    return arb(fmpq(q.numerator, q.denominator))


# ------------------------------------------------------------------ planar helpers (ball arithmetic)
def padd(a, b): return (a[0] + b[0], a[1] + b[1])
def psub(a, b): return (a[0] - b[0], a[1] - b[1])
def smul(t, a): return (t * a[0], t * a[1])
def dot(a, b): return a[0] * b[0] + a[1] * b[1]
def norm2(a): return a[0] * a[0] + a[1] * a[1]
def sqrt_nn(x):
    """sqrt of a mathematically nonnegative quantity (the ball may straddle 0 after rounding: intersect with [0, inf) first)."""
    return x.nonnegative_part().sqrt()


def dist(a, b): return sqrt_nn(norm2(psub(a, b)))
def cross(a, b): return a[0] * b[1] - a[1] * b[0]


def lt(a, b): return bool(a < b)        # certain comparisons (arb semantics)
def le(a, b): return bool(a <= b)
def ge(a, b): return bool(a >= b)


def bmax(*xs):
    m = xs[0]
    for x in xs[1:]:
        m = m.max(x)
    return m


def angle_le_120_vec(u, v):
    """certainly angle(u, v) <= 120 degrees."""
    d = dot(u, v)
    if d >= 0:
        return True
    return bool(FOUR * d * d <= norm2(u) * norm2(v))


def angle_le_120(a, b, c):
    return angle_le_120_vec(psub(a, b), psub(c, b))


def rot60(u):
    c, s = ONE / TWO, SQ3 / TWO
    return (c * u[0] - s * u[1], s * u[0] + c * u[1])


def smt3(a, b, c):
    """upper bound of the Steiner minimal tree length of three points."""
    if not angle_le_120(a, b, c):
        return dist(a, b) + dist(b, c)
    if not angle_le_120(b, c, a):
        return dist(b, c) + dist(c, a)
    if not angle_le_120(c, a, b):
        return dist(c, a) + dist(a, b)
    S = abs(cross(psub(b, a), psub(c, a))) / TWO
    return sqrt_nn((norm2(psub(a, b)) + norm2(psub(b, c)) + norm2(psub(c, a))) / TWO + TWO * SQ3 * S)


DIR0 = (ONE, arb(0))
DIR1 = (ONE / TWO, SQ3 / TWO)
DIR2 = (ONE / TWO, -SQ3 / TWO)


# ------------------------------------------------------------------ the two case families
class Family:
    def __init__(self, name):
        self.name = name
        if name == "d_steiner":
            self.nodes = ["A", "B", "D", "U", "V", "P", "Q", "R", "s", "r", "X", "Y"]
            self.edges = [("A", "s"), ("B", "s"), ("r", "P"), ("r", "D"), ("s", "r"), ("D", "U"), ("D", "V"), ("P", "R"), ("P", "Q")]
            self.vars = ["b", "c", "d", "s", "u", "v", "e", "f"]
            self.ynode = "V"
        elif name == "d_regular":
            self.nodes = ["A", "B", "D", "P", "Q", "R", "s", "r", "X", "Y"]
            self.edges = [("A", "s"), ("B", "s"), ("r", "P"), ("r", "D"), ("s", "r"), ("P", "R"), ("P", "Q")]
            self.vars = ["b", "c", "d", "s", "e", "f"]
            self.ynode = "D"
        else:
            raise ValueError("family")
        self.nid = {c: i for i, c in enumerate(self.nodes)}
        self.vid = {c: i for i, c in enumerate(self.vars)}
        self.eid = {self.nedge(u, v): i for i, (u, v) in enumerate(self.edges)}   # 0-based; edge 0 = (A,s) has length 1
        self.lemmas = self.build_lemmas()

    def nedge(self, u, v):
        a, b = self.nid[u], self.nid[v]
        return (a, b) if a < b else (b, a)

    def coords(self, V):
        g = dict(zip(self.vars, V))
        A = (arb(0), arb(0)); s = (ONE, arb(0))
        P = {}
        P["A"] = A; P["s"] = s
        P["B"] = padd(s, smul(g["b"], DIR1))
        P["r"] = padd(s, smul(g["s"], DIR2))
        P["P"] = padd(P["r"], smul(-g["c"], DIR1))
        P["D"] = padd(P["r"], smul(g["d"], DIR0))
        if self.name == "d_steiner":
            P["U"] = padd(P["D"], smul(g["u"], DIR1))
            P["V"] = padd(P["D"], smul(g["v"], DIR2))
        P["Q"] = padd(P["P"], smul(g["f"], DIR2))
        P["R"] = padd(P["P"], smul(-g["e"], DIR0))
        return P

    # -------------------------------------------------------------- lemma tables (transcribed from lemmas/lemma_k.jl)
    def build_lemmas(self):
        fam = self.name
        Y = self.ynode            # trapped point Y hangs off V (d_steiner) or D (d_regular)

        def x_cond0(P, g, fval): return le(g["c"], ONE)
        def ax0(P, g): return bmax(dist(P["A"], P["r"]), dist(P["A"], P["P"]))
        def y_cond0(P, g, fval): return fval == 1
        if fam == "d_steiner":
            def y0(P, g): return bmax(dist(P["V"], P["r"]), dist(P["V"], P["P"]), dist(P["V"], P["Q"]))
        else:
            def y0(P, g): return bmax(dist(P["D"], P["P"]), dist(P["D"], P["Q"]))

        def x_cond1(P, g, fval):
            c, e, s = g["c"], g["e"], g["s"]
            return lt(e, ONE - c + TWO / SQ3 * s) and ge(c + e, ONE)

        def ax12(P, g):
            c, e = g["c"], g["e"]
            return bmax(dist(P["A"], P["s"]), dist(P["A"], P["r"]), dist(P["A"], P["P"]), dist(P["A"], P["R"]),
                        SQ3 / TWO * (c + e - ONE))

        def x_cond2(P, g, fval):
            c, e = g["c"], g["e"]
            return lt(e, ONE + (TWO / SQ3 - ONE) * c) and ge(c + e, ONE)

        def st_cond3(P, g, fval):
            c, d, s, e = g["c"], g["d"], g["s"], g["e"]
            Vp = padd(P["D"], rot60(psub(P["Q"], P["D"])))
            return (ge(c + e, ONE) and le(e, s + c + d + TWO) and ge(e, TWO - c - d + s)
                    and le(e * (TWO + c + THREE * d + s), TWO + c * c + THREE * d + TWO * s + THREE * c * s + THREE * d * s + TWO * s * s)
                    and le(e, THREE * s)
                    and angle_le_120_vec(psub(P["D"], P["R"]), psub(P["Q"], P["A"]))
                    and angle_le_120(P["A"], P["R"], Vp) and angle_le_120(P["R"], P["A"], Vp))

        def st_len3(P, g):
            c, d, s, e = g["c"], g["d"], g["s"], g["e"]
            x = (ONE + e + THREE * d + TWO * s + THREE * c) / TWO
            y = -SQ3 * (c + d + e - ONE) / TWO
            return sqrt_nn(x * x + y * y)

        def st_cond4(P, g, fval): return ge(g["c"], ONE) and ge(g["e"], ONE)

        def st_len4(P, g):
            S = ONE + g["s"] + g["c"] + g["e"] + TWO * g["d"]
            return sqrt_nn(S * S - S + ONE)

        def x_cond5(P, g, fval): return lt(g["e"], (TWO / SQ3 - ONE) * g["c"])
        def ax5(P, g): return bmax(dist(P["A"], P["r"]), dist(P["A"], P["P"]), dist(P["A"], P["R"]))

        def hx5(P, g, who):
            H = psub(P["R"], smul((g["c"] - g["e"]) / TWO, DIR2))
            W = P[who]
            return bmax(dist(W, P["r"]), dist(W, P["P"]), dist(W, P["R"]), dist(W, H))

        def st_cond6(P, g, fval): return ge(g["d"], g["b"])

        def st_len6(P, g):
            b, c, d, s, e = g["b"], g["c"], g["d"], g["s"], g["e"]
            t1 = TWO * b + c + TWO * d + e + s
            t2 = c + TWO * d + e + s
            return sqrt_nn(t1 * t1 + THREE * t2 * t2) / TWO

        def st_cond7(P, g, fval):
            c, d, s, e = g["c"], g["d"], g["s"], g["e"]
            k = c + s + TWO * d
            return (ge(d * (c + e - ONE) + e * (s + c), arb(0))
                    and ge(e, (sqrt_nn(k * k + FOUR * d) - k) / TWO)
                    and ge(-(TWO + s - c + d) * (c + TWO * e + TWO * d) + THREE * c * (s + c + d), arb(0))
                    and ge(s + e, ONE)
                    and le(c, ONE + d + (s + e) / TWO))

        def st_len7(P, g):
            S = TWO * g["d"] + g["s"] + g["c"] + g["e"]
            return sqrt_nn(S * S + S + ONE)

        def x_cond8(P, g, fval): return lt(g["e"], g["s"] + ONE)
        def ax8(P, g): return bmax(dist(P["A"], P["r"]), dist(P["A"], P["P"]), dist(P["A"], P["R"]), g["e"] + g["c"] - ONE)

        AX = self.nedge("A", "X"); YY = self.nedge(Y, "Y")
        ADQR = tuple(sorted(self.nid[c] for c in "ADQR")); BDQR = tuple(sorted(self.nid[c] for c in "BDQR"))
        L = [dict() for _ in range(9)]
        L[0] = {AX: (x_cond0, ax0), YY: (y_cond0, y0)}
        L[1] = {AX: (x_cond1, ax12)}
        L[2] = {AX: (x_cond2, ax12)}
        L[3] = {ADQR: (st_cond3, st_len3)}
        L[4] = {ADQR: (st_cond4, st_len4)}
        if fam == "d_steiner":
            L[5] = {AX: (x_cond5, ax5), self.nedge("U", "X"): (x_cond5, lambda P, g: hx5(P, g, "U")),
                    self.nedge("V", "X"): (x_cond5, lambda P, g: hx5(P, g, "V"))}
        else:
            L[5] = {AX: (x_cond5, ax5), self.nedge("D", "X"): (x_cond5, lambda P, g: hx5(P, g, "D"))}
        L[6] = {BDQR: (st_cond6, st_len6)}
        L[7] = {ADQR: (st_cond7, st_len7)}
        L[8] = {AX: (x_cond8, ax8)}
        for k in range(1, 9):
            if YY not in L[k]:
                L[k][YY] = (y_cond0, y0)       # verify_certificate.jl adds the lemma-0 Y bound to every lemma set
        return L


# ------------------------------------------------------------------ splits
class Split:
    __slots__ = ("V_star", "S_minus", "S_plus", "T_star", "mono", "mono_file")


def read_splits(fam, path):
    out = []
    for ln, line in enumerate(open(path)):
        line = line.strip()
        if not line:
            continue
        parts = {}
        for seg in line.split(";"):
            if ":" not in seg:
                continue
            k, v = seg.split(":", 1)
            parts[k.strip()] = ast.literal_eval(v.strip())
        sp = Split()
        sp.V_star = [fam.nid[u] for u in parts["V_star"]]
        sp.S_minus = [fam.eid[fam.nedge(u, v)] for (u, v) in parts["S_minus"]]
        splus = parts["S_plus"]
        sp.S_plus = tuple(sorted(fam.nid[u] for u in (list(splus) if isinstance(splus, (tuple, list)) else [splus])))
        sp.T_star = [fam.nedge(u, v) for (u, v) in parts["T_star"]]
        sp.mono_file = set(fam.vid[x] for x in parts["mono_vars"])
        out.append(sp)
    # monotone variables: our own derivation (mono43.py), not the file's claim
    import mono43
    for sp in out:
        sp.mono = mono43.derive(fam, sp, fam.name)
    return out


# ------------------------------------------------------------------ evaluation
def evaluate(fam, sp, V, lemma_id, rho, fval):
    """value of rho L(T*) + L(S+) - L(S-) at the arb vector V (ball semantics); None if a lemma condition fails."""
    P = fam.coords(V)
    g = dict(zip(fam.vars, V))
    names = fam.nodes
    imp = (fam.nid["X"], fam.nid["Y"])
    lem = fam.lemmas[lemma_id]
    t = arb(0)
    for (a, b) in sp.T_star:
        if a in imp or b in imp:
            cf = lem.get((a, b))
            if cf is None or not cf[0](P, g, fval):
                return None
            t += cf[1](P, g)
        else:
            t += dist(P[names[a]], P[names[b]])
    sm = arb(0)
    for idx in sp.S_minus:
        sm += ONE if idx == 0 else V[idx - 1]
    k = len(sp.S_plus)
    if k <= 1:
        sp_len = arb(0)                             # empty or single-point S+ (as in verify_certificate.jl: s_plus stays 0)
    elif k == 2:
        sp_len = dist(P[names[sp.S_plus[0]]], P[names[sp.S_plus[1]]])
    elif k == 3:
        sp_len = smt3(*(P[names[i]] for i in sp.S_plus))
    else:
        cf = lem.get(sp.S_plus)
        if cf is None or not cf[0](P, g, fval):
            return None
        sp_len = cf[1](P, g)
    return rho * t + sp_len - sm


def check_record(fam, splits, rec, n, fval, rho, fullbox):
    """returns (status, detail): status in ok_vertex, ok_fullbox, skipped_symmetry, skipped_subcase, fail."""
    rid, box, split_id, lemma_id = rec
    vi = fam.vid
    if fam.name == "d_steiner" and max(box[vi["u"]][0], box[vi["v"]][0]) > max(box[vi["b"]][1], 1.0):
        return "skipped_symmetry", None
    if fval == 1 and box[vi["f"]][0] > box[vi["d"]][1]:
        return "skipped_subcase", None
    if not (1 <= split_id <= len(splits)) or not (0 <= lemma_id <= 8):
        return "fail", "bad split or lemma id"
    sp = splits[split_id - 1]
    if fval == 2 and vi["f"] not in sp.mono:
        return "fail", "f >= d but f not monotone"
    if fval == 1 and len(sp.S_plus) > 3:
        return "fail", "f <= d with |S+| > 3"
    for i in range(n):
        lo, hi = box[i]
        if not (lo <= hi):
            return "fail", "empty box"
        if hi == float("inf") and (i not in sp.mono or lemma_id > 0):
            return "fail", "infinite end without monotonicity / lemma 0"
    full = len(fam.vars)
    nv = 0
    for mask in range(1 << n):
        V = [None] * full
        finite = True
        for i in range(n):
            x = box[i][(mask >> i) & 1]
            if x == float("inf"):
                finite = False
                break
            V[i] = arb(x)                           # box ends are doubles: exact as arb
        if not finite:
            continue
        if fval == 2:
            V[vi["f"]] = V[vi["d"]]
        val = evaluate(fam, sp, V, lemma_id, rho, fval)
        nv += 1
        if val is None or not (val <= 0):
            return "fail", f"vertex mask {mask}: {'condition fails' if val is None else val.str(5)}"
    if fullbox and all(box[i][1] != float("inf") for i in range(n)):
        if fullbox_check(fam, sp, box, n, fval, rho, lemma_id, fullbox):
            return "ok_fullbox", nv
    return "ok_vertex", nv


def fullbox_check(fam, sp, box, n, fval, rho, lemma_id, budget):
    """F <= 0 on the whole box (direct ball evaluation, bisection of the widest side, at most `budget` sub-boxes)."""
    vi = fam.vid
    stack = [[(box[i][0], box[i][1]) for i in range(n)]]
    used = 0
    while stack:
        b = stack.pop()
        used += 1
        if used > budget:
            return False
        V = [None] * len(fam.vars)
        for i in range(n):
            lo, hi = b[i]
            V[i] = arb(lo).union(arb(hi))
        if fval == 2:
            V[vi["f"]] = V[vi["d"]]
        val = evaluate(fam, sp, V, lemma_id, rho, fval)
        if val is not None and val <= 0:
            continue
        j = max(range(n), key=lambda i: b[i][1] - b[i][0])
        m = (b[j][0] + b[j][1]) / 2
        if not (b[j][0] < m < b[j][1]):
            return False
        b1 = list(b); b2 = list(b)
        b1[j] = (b[j][0], m); b2[j] = (m, b[j][1])
        stack += [b1, b2]
    return True


# ------------------------------------------------------------------ driver
def rec_size(n):
    return 4 + 16 * n + 8


def read_records(path, n, start, count):
    sz = rec_size(n)
    fmt = "<I" + "d" * (2 * n) + "ii"
    with open(path, "rb") as fh:
        fh.seek(start * sz)
        k = 0
        while count is None or k < count:
            raw = fh.read(sz)
            if len(raw) < sz:
                break
            t = struct.unpack(fmt, raw)
            box = [(t[1 + 2 * i], t[2 + 2 * i]) for i in range(n)]
            yield (t[0], box, t[1 + 2 * n], t[2 + 2 * n])
            k += 1


G = {}
def init(args):
    fam_name, splits_path, rho_s, n, fval, fullbox = args
    flint.ctx.prec = 128
    G["fam"] = Family(fam_name)
    G["splits"] = read_splits(G["fam"], splits_path)
    G["rho"] = ex(Fr(rho_s))
    G["n"] = n; G["fval"] = fval; G["fullbox"] = fullbox


def work(task):
    path, start, count = task
    fam, splits, rho, n, fval, fb = G["fam"], G["splits"], G["rho"], G["n"], G["fval"], G["fullbox"]
    cnt = {}
    fails = []
    t0 = time.time()
    for rec in read_records(path, n, start, count):
        st, det = check_record(fam, splits, rec, n, fval, rho, fb)
        cnt[st] = cnt.get(st, 0) + 1
        if st == "fail" and len(fails) < 20:
            fails.append({"region": rec[0], "box": rec[1], "split": rec[2], "lemma": rec[3], "why": det})
    return {"start": start, "count": count, "cnt": cnt, "fails": fails, "sec": round(time.time() - t0, 2)}


def main():
    a = [x for x in sys.argv[1:] if not x.startswith("--")]
    opts = dict(x[2:].split("=", 1) for x in sys.argv[1:] if x.startswith("--") and "=" in x)
    fam_name, sub, splits_path, cert, rho_s, nproc, out = a[0], a[1], a[2], a[3], a[4], int(a[5]), a[6]
    fam = Family(fam_name)
    fval = 2 if sub == "f_ge_d" else 1
    n = len(fam.vars) - (1 if fval == 2 else 0)
    fullbox = int(opts.get("fullbox", "0"))
    total = os.path.getsize(cert) // rec_size(n)
    if os.path.getsize(cert) % rec_size(n):
        sys.exit("FAIL: certificate size is not a multiple of the record size")
    start = int(opts.get("start", "0")); limit = int(opts.get("limit", str(total - start)))
    chunk = 20000
    tasks = [(cert, s, min(chunk, start + limit - s)) for s in range(start, start + limit, chunk)]
    print(f"{fam_name} {sub}: n = {n}, {total} records in {cert}; checking [{start}, {start + limit}) at rho = {rho_s}, "
          f"fullbox budget {fullbox}, {len(tasks)} tasks", flush=True)
    import multiprocessing as mp
    tot = {}; nfail = 0; t0 = time.time(); done = 0
    with mp.get_context("spawn").Pool(nproc, initializer=init, initargs=((fam_name, splits_path, rho_s, n, fval, fullbox),)) as pool, \
            open(out, "w") as fo:
        for r in pool.imap_unordered(work, tasks, chunksize=1):
            fo.write(json.dumps(r) + "\n")
            for k, v in r["cnt"].items():
                tot[k] = tot.get(k, 0) + v
            nfail += r["cnt"].get("fail", 0)
            done += 1
            if done % max(1, len(tasks) // 50) == 0:
                print(f"  [{time.time() - t0:8.0f}s] {done}/{len(tasks)} tasks {json.dumps(tot)}", flush=True)
    print(f"totals {json.dumps(tot, sort_keys=True)}; wall {time.time() - t0:.0f}s")
    print("RESULT:", "ALL RECORDS PASS" if nfail == 0 and sum(tot.values()) == limit else f"{nfail} FAILURES")


if __name__ == "__main__":
    main()
