#!/usr/bin/env python3
"""mono43.py: independent derivation of each split's monotone variables, for the vertex reduction on unbounded boxes
and the f >= d -> f = d reduction. With all points affine in the edge lengths, increasing an edge length t translates the part of the
configuration tree beyond that edge, so along t (others fixed) the split function is convex with asymptotic slope
    rho * n_T + d_plus - d_minus,
n_T = number of T* terms whose two ends the edge separates (trapped-point terms: their lemma-0 bound depends on the edge, i.e. slope 1),
d_plus = 1 if the edge separates the S+ points (the S+ length moves at asymptotic rate <= 1), d_minus = 1 if the edge is in S-.
A convex function with asymptotic slope <= 0 is non-increasing. For 1/2 < rho < 1 the slope is <= 0 exactly when
n_T + d_plus = d_minus = 0, or n_T + d_plus <= 1 and d_minus = 1 (the original's rule; derived here independently).
Trapped-point terms are allowed on unbounded boxes only with lemma 0 (bounds: A-X max(|Ar|,|AP|); Y: d_steiner max(|Vr|,|VP|,|VQ|),
d_regular max(|DP|,|DQ|)); their edge dependence is computed from the coordinates, not assumed.
usage: python3 -I -B mono43.py FAMILY SPLITS.txt   (prints the derived masks' comparison with the file's mono_vars)"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

TREE = {
    "d_steiner": [("A", "s"), ("B", "s"), ("s", "r"), ("r", "D"), ("r", "P"), ("P", "Q"), ("P", "R"), ("D", "U"), ("D", "V")],
    "d_regular": [("A", "s"), ("B", "s"), ("s", "r"), ("r", "D"), ("r", "P"), ("P", "Q"), ("P", "R")],
}
VAR_EDGE = {"b": ("B", "s"), "s": ("s", "r"), "c": ("r", "P"), "d": ("r", "D"), "u": ("D", "U"), "v": ("D", "V"),
            "e": ("P", "R"), "f": ("P", "Q")}


def side(fam_name, edge, root="A"):
    """set of tree nodes on the far side of `edge` from `root`."""
    adj = {}
    for a, b in TREE[fam_name]:
        adj.setdefault(a, []).append(b); adj.setdefault(b, []).append(a)
    u, v = edge
    # the side containing v after removing u-v
    seen = {v}; stack = [v]
    while stack:
        x = stack.pop()
        for y in adj.get(x, []):
            if {x, y} == {u, v} or y in seen:
                continue
            seen.add(y); stack.append(y)
    return seen


def separates(fam_name, edge, pts):
    far = side(fam_name, edge)
    k = sum(1 for p in pts if p in far)
    return 0 < k < len(pts)


def trapped_dep(fam_name, a, b):
    """variables whose edge the lemma-0 bound of trapped term (a, b) depends on (computed from which configuration points it uses)."""
    if {a, b} == {"A", "X"}:
        pts = [("A", "r"), ("A", "P")]
    elif {a, b} == ({"V", "Y"} if fam_name == "d_steiner" else {"D", "Y"}):
        pts = [("V", "r"), ("V", "P"), ("V", "Q")] if fam_name == "d_steiner" else [("D", "P"), ("D", "Q")]
    else:
        return None       # not a lemma-0 term: never allowed on unbounded boxes; for f it is checked separately below
    dep = set()
    for var, edge in VAR_EDGE.items():
        if edge[0] not in {x for e in TREE[fam_name] for x in e} or edge[1] not in {x for e in TREE[fam_name] for x in e}:
            continue
        if any(separates(fam_name, edge, [p, q]) for p, q in pts):
            dep.add(var)
    return dep


def lemma_any_dep_f(fam_name, a, b):
    """does any lemma's bound for trapped term (a, b) use Q (the only point moved by f)?  X-terms: A, U, V, D, s, r, P, R, H(R) -> no;
    Y-term: uses Q -> yes."""
    return "Y" in (a, b)


def derive(fam, sp, fam_name):
    names = fam.nodes
    mono = set()
    for var, edge in VAR_EDGE.items():
        if var not in fam.vid:
            continue
        nT = 0; ok = True
        for (ia, ib) in sp.T_star:
            a, b = names[ia], names[ib]
            if "X" in (a, b) or "Y" in (a, b):
                dep = trapped_dep(fam_name, a, b)
                if var == "f":
                    if lemma_any_dep_f(fam_name, a, b):
                        nT += 1
                    continue
                if dep is None:
                    ok = False          # non-lemma-0 trapped term: the variable cannot be treated as monotone
                    continue
                if var in dep:
                    nT += 1
            elif separates(fam_name, edge, [a, b]):
                nT += 1
        splus = [names[i] for i in sp.S_plus]
        dplus = 1 if len(splus) >= 2 and separates(fam_name, edge, splus) else 0
        dminus = 1 if fam.eid[fam.nedge(*edge)] in sp.S_minus else 0
        if ok and ((nT + dplus == 0 and dminus == 0) or (nT + dplus <= 1 and dminus == 1)):
            mono.add(fam.vid[var])
    return mono


if __name__ == "__main__":
    import indep43 as I
    fam_name, path = sys.argv[1], sys.argv[2]
    fam = I.Family(fam_name)
    sp = I.read_splits(fam, path)
    mism = 0; extra_theirs = 0; extra_ours = 0
    for i, s in enumerate(sp):
        ours = derive(fam, s, fam_name)
        if ours != s.mono:
            mism += 1
            if s.mono - ours:
                extra_theirs += 1
            if ours - s.mono:
                extra_ours += 1
            if mism <= 5:
                print(f"split {i + 1}: file {sorted(fam.vars[j] for j in s.mono)} derived {sorted(fam.vars[j] for j in ours)}")
    print(f"{fam_name}: {len(sp)} splits; mono sets differ on {mism} (file claims more: {extra_theirs}; derived more: {extra_ours})")
