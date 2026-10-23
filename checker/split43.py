#!/usr/bin/env python3
"""split43.py: independent combinatorial check that every split of a PKU splits.txt is a splitting in the sense of
arXiv:2601.22365 Def. 13 (= Du-Hwang 1983 Lemma 3) on the local configuration tree, with the trapped terminals X (in the residual
subtree at R) and Y (in the residual subtree at Q) as terminals of V \\ V*:
  1. V* is a non-empty subset of the known terminals (d_steiner: A, B, U, V; d_regular: A, B, D), so V* is a proper subset of V;
  2. S- is a set of configuration-tree edges; 3. after deleting S-, no point of V* has an incident edge left;
  4. S+ avoids V*, and the terminals outside V* (incl. X, Y, i.e. the residual subtrees at R and Q, which stay connected internally)
     are connected in (tree - S-) + S+ (S+ joins its points);
  5. T* is a forest whose vertices are terminals (known ones or X, Y), and T* with all of V \\ V* contracted to one vertex is a tree
     on V* + {super}: every x in V* reaches V \\ V*, and no T* path joins two distinct terminals of V \\ V*.
usage: python3 -I -B split43.py FAMILY SPLITS.txt"""
import sys, ast

CONF = {
    "d_steiner": dict(edges=[("A", "s"), ("B", "s"), ("s", "r"), ("r", "D"), ("r", "P"), ("P", "Q"), ("P", "R"), ("D", "U"), ("D", "V")],
                      known=["A", "B", "U", "V"]),
    "d_regular": dict(edges=[("A", "s"), ("B", "s"), ("s", "r"), ("r", "D"), ("r", "P"), ("P", "Q"), ("P", "R")],
                      known=["A", "B", "D"]),
}


def parse(line):
    d = {}
    for seg in line.strip().split(";"):
        if ":" in seg:
            k, v = seg.split(":", 1)
            d[k.strip()] = ast.literal_eval(v.strip())
    sp = d["S_plus"]
    d["S_plus"] = list(sp) if isinstance(sp, (list, tuple)) else [sp]
    return d


def comps(nodes, edges):
    parent = {x: x for x in nodes}
    def f(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for a, b in edges:
        ra, rb = f(a), f(b)
        if ra != rb:
            parent[ra] = rb
    return f


def check(fam, d):
    C = CONF[fam]
    E = {frozenset(e) for e in C["edges"]}
    known = set(C["known"])
    term_out_names = {"X": "R", "Y": "Q"}     # trapped terminals live in the residual subtrees rooted at R and Q
    Vs = set(d["V_star"]); Sm = [frozenset(e) for e in d["S_minus"]]; Sp = d["S_plus"]; Ts = d["T_star"]
    err = []
    if not Vs or not Vs <= known:
        err.append("V* empty or not a subset of the known terminals")
    if any(e not in E for e in Sm):
        err.append("S- edge not in the tree")
    rem = [tuple(e) for e in E if e not in Sm]
    for x in Vs:
        if any(x in e for e in rem):
            err.append(f"V* point {x} keeps an edge"); break
    if set(Sp) & Vs:
        err.append("S+ meets V*")
    nodes = {x for e in C["edges"] for x in e}
    if any(p not in nodes for p in Sp):
        err.append("S+ point not in the configuration")
        return err
    # connectivity of terminals outside V*: known \ V* plus R, Q (standing for X, Y) in (tree - S-) + S+
    joins = rem + [(Sp[0], p) for p in Sp[1:]]
    f = comps(nodes, joins)
    outside = [x for x in known if x not in Vs] + ["R", "Q"]
    if len({f(x) for x in outside}) != 1:
        err.append("terminals outside V* not connected by (tree - S-) + S+")
    # T*: vertices must be terminals (known or X/Y)
    tnodes = {x for e in Ts for x in e}
    if any(x not in known and x not in ("X", "Y") for x in tnodes):
        err.append("T* uses a non-terminal")
    # forest + contraction test
    def m(x): return x if x in Vs else "SUPER"
    cnodes = set(Vs) | {"SUPER"}
    parent = {x: x for x in cnodes}
    def g(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    nedges = 0
    for a, b in Ts:
        ma, mb = m(a), m(b)
        if ma == mb:
            err.append("T* edge inside V \\ V* or a loop"); break
        ra, rb = g(ma), g(mb)
        if ra == rb:
            err.append("T* contracted has a cycle (or V \\ V* joined twice)"); break
        parent[ra] = rb; nedges += 1
    if len({g(x) for x in cnodes}) != 1:
        err.append("T* contracted is disconnected (some V* point not linked to V \\ V*)")
    return err


if __name__ == "__main__":
    fam, path = sys.argv[1], sys.argv[2]
    bad = 0; n = 0
    for i, line in enumerate(open(path)):
        if not line.strip():
            continue
        n += 1
        e = check(fam, parse(line))
        if e:
            bad += 1
            if bad <= 10:
                print(f"split {i + 1}: {e}")
    print(f"{fam}: {n} splits, {bad} invalid")
