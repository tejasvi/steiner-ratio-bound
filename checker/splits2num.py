#!/usr/bin/env python3
"""splits2num.py: convert a PKU splits.txt into the numeric format read by indep43c (one split per line):
   nS- e_1 .. e_k  nS+ v_1 .. v_m  nT* a_1 b_1 .. a_t b_t  monomask
edge ids are 0-based positions in the family's edge list ((A,s) = 0), node ids are positions in the family's node list (S+ sorted,
T* pairs normalised a < b), monomask has bit i for case variable i (OUR derived monotone set, mono43.py; the file's mono_vars are not used).
Uses indep43.read_splits (same parsing as the Python checker).
usage: python3 -I -B splits2num.py FAMILY SPLITS.txt OUT.num"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import indep43 as I

fam = I.Family(sys.argv[1])
sp = I.read_splits(fam, sys.argv[2])
with open(sys.argv[3], "w") as fo:
    for s in sp:
        mask = sum(1 << i for i in s.mono)
        parts = [str(len(s.S_minus))] + [str(e) for e in s.S_minus]
        parts += [str(len(s.S_plus))] + [str(v) for v in s.S_plus]
        parts += [str(len(s.T_star))] + [str(x) for pr in s.T_star for x in pr]
        parts += [str(mask)]
        fo.write(" ".join(parts) + "\n")
print(f"{len(sp)} splits written to {sys.argv[3]}")
