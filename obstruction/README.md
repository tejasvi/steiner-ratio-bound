# Programs for Proposition 6.1

These programs evaluate the splitting functions of Ke, Huang, Shu, He, Gai and Wang (arXiv:2601.22365) for the
d_regular configuration with f = d at two points with rational coordinates:

```
w* = (b, c, d, s, e) = (13656/10000, 110927/100000, 365604/1000000, 1, 171605/1000000)
w1 = (b, c, d, s, e) = (134514/100000, 107421/100000, 347656/1000000, 100391/100000, 167969/1000000)
```

For a splitting and a lemma set, the cost bound rho L(t*) + L(S+) - L(S-) is affine in rho; its critical value is
(L(S-) - L(S+)) / L(t*).

`./run.sh PYTHON` reproduces `out/` in a few seconds on one core. It needs python-flint and g++.

- `tools/obstruction.py` works in ball arithmetic with 128-bit precision.
  - It evaluates all 158 x 9 = 1,422 pairs of a splitting of the d_regular table (`tools/splits/d_regular_splits.txt`,
    the file of Ke et al.) and a lemma set, with the lemma formulas as transcribed in `tools/indep43.py`. At both points
    the conditions of 527 pairs hold, and each of them has a positive cost bound at rho = 0.856 (at w*) or 0.8572 (at
    w1). The largest critical values, 0.855986741241... and 0.857134921267..., are attained by splitting 48 (line 48 of
    the table). Output: `out/way1_wstar.txt`, `out/way1_w1.txt`. The files `out/way1_linear_conditions_only_*.txt` repeat
    the computation with the conditions of lemma sets 3 and 7, which are not linear, ignored; the result is the same.
    The files `out/way1_no_conditions_*.txt` ignore all conditions and are for information only.
  - It enumerates the 42,303 combinations of Proposition 6.1(b) with lower bounds for L(S+): the distance, the length
    of a Steiner minimal tree for three points, and for four points the largest of several valid lower bounds, among
    them one from the dual of the network problem (see the docstring). Output: `out/way3_wstar.txt`, `out/way3_w1.txt`,
    with the upper bounds 0.855986741241280 and 0.857134921266727 for the critical values.
- `tools/ceilpt/ceilpt.cpp` evaluates the formulas of Ke et al. (`tools/ceilpt/formulas/`, unchanged) in double
  precision at the same points and finds the same largest values (`out/way2.txt`).
- `out/summary.txt` has one line per computation.

`tools/indep43.py` and `tools/mono43.py` are the same programs as in `checker/`. The formulas in
`tools/ceilpt/formulas/` and the parts of `ceilpt.cpp` taken from the generator of Ke et al. are under the MIT
License, Copyright (c) 2025-2026 Yisi Ke and Yankai Shu (`tools/ceilpt/LICENSE_PKU_MIT.txt`); the split table is their
file `certificate/d_regular/splits.txt`.
