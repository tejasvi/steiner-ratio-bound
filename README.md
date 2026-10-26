# Certificates, programs and Lean formalization for "The Steiner ratio is at least 0.8564"

This repository contains the programs, splitting tables, logs and control runs of the computer-assisted part of the
paper, the programs behind its Proposition 6.1, and the two formal proofs of Section 7 in Lean 4: one with checks run as
compiled code (`lean/`) and one with all checks run in the Lean kernel (`lean_kernel/`). The paper is archived at
doi:10.5281/zenodo.23644989. The certificate files, the data files of the formal proofs, the hash lists of the kernel-checked
proof and a copy of this repository are archived at doi:10.5281/zenodo.23644994.

The proof follows the method of Ke, Huang, Shu, He, Gai and Wang (arXiv:2601.22365, ICML 2026), whose code is at
https://github.com/keyisi2006/Steiner-Ratio. The splitting tables and the generator of boxes come from that code; see
"Provenance and licences" below.

## What is checked where

| paper | statement | files |
|---|---|---|
| Theorem 1.1, Section 5.4 | every record passes the checker at rho = 2141/2500 | certificate files (archive), `checker/indep43c.c`, `logs/<family>/verify3/` |
| Theorem 1.1, Section 5.3 | the boxes of each family tile [0, inf)^n | certificate files (archive), `checker/cover43.c`, `logs/<family>/verify/cover.out` |
| Section 4.1 | the splittings of the tables have the properties listed there | `splits/*_splits.txt`, `checker/split43.py` |
| Section 4.3 | the monotone coordinates of each splitting | `checker/mono43.py`, `checker/splits2num.py`, `splits/*.num` |
| Section 5.4 | the control runs | `controls/` |
| Proposition 6.1 | the obstruction at w* and w1 | `obstruction/` |
| Sections 2-3, Remark 3.9 | identities used in the proofs; the two examples of the remark | `checks/` |
| Section 7 | Theorem 1.1 from the hypotheses (H1)-(H3) (`S43.Final.steiner_ratio_ge`) and the certificate theorem (`S43.Final.certificate`), with checks run as compiled code | `lean/`, data files of the formal proofs (archive) |
| Section 7.1 | the same two theorems with all checks run in the Lean kernel (`S43K.Final.steiner_ratio_ge`, `S43K.Final.certificate`) | `lean_kernel/`, data files of the formal proofs and hash lists (archive) |

## The certificate files

There are four families. Each has a record file and a tree file:

| family | n | coordinates | records | record file | tree file |
|---|---|---|---|---|---|
| d_regular, f <= d (`d_regular f_le_d`) | 6 | b, c, d, s, e, f | 95,569,010 | `d_regular_f_le_d_certificate.bin` | `d_regular_f_le_d_child.bin` |
| d_regular, f >= d (`d_regular f_ge_dv`) | 6 | b, c, d, s, e, f | 10,376,823 | `d_regular_f_ge_dv_certificate.bin` | `d_regular_f_ge_dv_child.bin` |
| d_steiner, f <= d (`d_steiner f_le_d`) | 8 | b, c, d, s, u, v, e, f | 436,460,311 | `d_steiner_f_le_d_certificate.bin` | `d_steiner_f_le_d_child.bin` |
| d_steiner, f >= d (`d_steiner f_ge_d`) | 7 | b, c, d, s, u, v, e (f = d) | 12,696,761 | `d_steiner_f_ge_d_certificate.bin` | `d_steiner_f_ge_d_child.bin` |

The archive holds the files compressed with xz (`<name>.bin.xz`); `xz -d` restores them. `MANIFEST.txt` lists, for
every file, the size and SHA-256 of the uncompressed file and of the compressed file. The uncompressed files have
94,104,688,256 bytes in total.

A record is a little-endian `uint64` identifier, then n pairs of `double` (lower and upper end of the box in each
coordinate, the upper end possibly +inf), then an `int32` splitting number (the line of `splits/<family>.num`,
counted from 1) and an `int32` lemma set (0 to 8). Records whose box lies outside the domain of the family may carry
the splitting number -1; the checker skips them. The tree file lists, for the identifiers N down to 1, a pair of
`uint64` (left child, right child), with (0, 0) for a leaf. The roots are the 2^n boxes whose sides are [0, 1] or
[1, inf), with identifiers 1 to 2^n; the coordinate along which a box is split and the split point are recomputed by
`checker/cover43.c`.

In the program sources and logs, the hidden terminals E and F of the paper are called X and Y, the Steiner points
X, Y, Z are called s, r, P, and Lemmas 3.11 and 3.12 are called X2 and Y2.

## Building and running the checks

The checker needs FLINT 3 (which contains Arb) and its headers; the runs used FLINT 3.1.3 and gcc.

```
gcc -O2 -DID64 -o indep43c checker/indep43c.c -lflint -lmpfr -lgmp -lm
gcc -O2 -DID64 -o cover43 checker/cover43.c -lm
```

Coverage of one family, with n as in the table above:

```
./cover43 d_regular_f_ge_dv_certificate.bin d_regular_f_ge_dv_child.bin 6
```

It prints `OK COVER` or the first failure. The checker reads a range of records and prints one JSON line with the
numbers of passed, skipped and failed records:

```
./indep43c d_regular f_ge_dv splits/d_regular.num d_regular_f_ge_dv_certificate.bin 2141 2500 0 0
```

The last two arguments are the first record and the number of records (0 for all). The four families are
`d_regular f_le_d`, `d_regular f_ge_dv`, `d_steiner f_le_d` and `d_steiner f_ge_d`. The runs split each family into
chunks of 500,000 records and checked the chunks in parallel (`runs/verify3.sh`); the chunk results are in
`logs/<family>/verify3/`. Checking all records takes about 200 core-hours, most of it for `d_steiner f_le_d`.

The `.num` files are produced from the tables by `checker/splits2num.py`, which uses `checker/indep43.py` and
`checker/mono43.py` and needs python-flint:

```
python3 checker/splits2num.py d_regular splits/d_regular_splits.txt d_regular.num
```

This reproduces `splits/d_regular.num` byte for byte, and likewise for `d_steiner`. The monotone coordinates in the
last column are derived by `mono43.py` from the rule of Section 4.3; the `mono_vars` column of the tables is not used.
`checker/split43.py FAMILY splits/FAMILY_splits.txt` checks the properties of Section 4.1 and reports 0 invalid
splittings for both tables.

## The Lean proofs

`lean/` is a Lean 4 project (Lean v4.35.0-rc3, Mathlib commit c55e6e786f49). Its theorem
`S43.Final.steiner_ratio_ge` says that (2141/2500) L_MST(P) <= L_SMT(P) for every finite set P of points of the plane,
for any relation `Real` (the realization of a configuration in a Steiner minimal tree, not the real numbers) that
satisfies the hypotheses `LemmaLayer Real` of `lean/S43/Statements.lean`:

- `HTrap`: the bounds of the lemma sets for the hidden terminals E and F hold under their conditions (Lemmas 3.4-3.8,
  with the conditions of Lemmas 3.6 and 3.11 for lemma set 5, and Lemma 3.12 for |DF| in d_regular);
- `HDomain`: the parameters of a configuration lie in the domain of its type (Lemma 2.5);
- `HDuHwang`: if every configuration has an entry of the tables with cost at most 0, the ratio bound holds for every
  finite set (Lemmas 2.2-2.5, the case of sets of at most four points in Section 2.6, the hidden terminals of Section 3.1,
  the table check of Section 4.1 and the induction of Section 5.5).

These are proved in the paper, except the check of the tables and their transcription into the numeric form used by
the checkers, which are done by `checker/split43.py` and `checker/splits2num.py`; in Lean all of them are hypotheses.
The rest is proved in Lean. In particular, `S43.Final.certificate` has no hypotheses: every parameter in the domain
of either configuration type has an entry of the table and a lemma set whose conditions hold there and whose cost
bound at 2141/2500 is at most 0, with the edges at E and F priced by the bounds of the lemma set. A checking program
written in Lean runs over all 555,102,905 leaves of the four trees, and a Lean proof shows that its acceptance implies
the certificate theorem. The runs of the program are evaluated by `native_decide`, so they execute compiled code; the
trusted base thus contains the Lean compiler and its interpreter, the C compiler it invokes, the Lean runtime and the
compiled core-library functions used by the checks. Apart from `propext`, `Classical.choice` and `Quot.sound`, the
final theorem rests on 496 axioms, each asserting that one compiled check returned true (`lean/evidence/axioms.txt`).
`lean/README.md` describes the files, the data and the build.

`lean_kernel/` holds the second proof, for the same versions of Lean and Mathlib. Its theorems
`S43K.Final.steiner_ratio_ge` and `S43K.Final.certificate` have the same statements as `S43.Final.steiner_ratio_ge` and
`S43.Final.certificate`, and it reuses the files in `lean/` that define the networks, boxes, tables and families and
prove the enclosure, convexity and covering arguments. Its checking program uses the same intervals as that of `lean/`,
stored as natural numbers shifted by 2^256 so that the kernel can evaluate it, and computes the points of its networks
by exact constructions instead of floating-point iterations. Every run of it is evaluated by the Lean kernel through
`decide +kernel`: there is one theorem per record, in generated modules of about 1,200 consecutive records, each of
which exports a single theorem about its part of the walk through the tree, and further generated modules chain these
parts for each family. Both theorems use only `propext`, `Classical.choice` and `Quot.sound`, and the proof relies on
Lean's kernel instead of code generated by Lean's compiler. The generated modules are not stored: the generator in
`lean_kernel/` produces them from the data files of the archive, and the hash lists in the archive
(`lean_kernel_lists.tar.xz`) allow every module and compiled file of a rebuild to be compared with those of the original
build. `lean_kernel/README.md` describes the files and the build.

## The generator

`generator/gen43f.cpp.tmpl` builds the trees. It is derived from the generator of Ke et al. (their files
`certificate/d_*/plot_f_*.cpp`) and includes their formulas for the splittings (`generator/formulas/`). We changed
the order in which splittings are tried, the distribution of the work over threads, the size of the identifiers and
the treatment of f >= d, and added Lemmas 3.11 and 3.12 and the explicit four-point networks. `runs/run_cert2.sh`
shows how it was built and run (`RHO_VAL` is replaced by 0.8564). `generator/est43f.cpp.tmpl` estimates the size of
a tree before a run. The generator is not part of the proof: its output is checked by `checker/indep43c.c` and
`checker/cover43.c`, which share no code with it.

## The logs

For each family, `logs/<family>/` contains:

- `gen.log`, `gen.out`, `gen.progress`, `gen.time` and `gen43f.cpp`: the generator run and its source.
- `verify3/`: the run of `checker/indep43c.c` on all records, in chunks; `verify.log` gives the totals. These are
  the results in the paper.
- `verify/`: the coverage result `cover.out`, and an earlier run of the checker (version 2, in
  `checker/history/`) on the same records. The version-2 run of `d_steiner f_le_d` was stopped after the final
  version was written, so its `verify.log` reports missing chunks; that family was then checked in full in `verify3/`.

`logs/run/` contains the summary lines of both checker runs (`ALL2.log`, `ALL3.log`) and the sizes, SHA-256 values
and CRC32C checksums of the certificate files computed on the machine that produced them (`HASH.log`). In the logs,
`<WORK>` stands for the working directory of the runs and `<host>` for the machine.

## Controls

`controls/` contains the control runs of Section 5.4:

- `controls_real2.log`: on the certificate files, with `runs/controls_real2.sh`. The first 2,000,000 records of
  each family are checked at rho = 2142/2500 and 4283/5000 (between 29,122 and 129,167 failures per run); in a copy
  of 100,000 records of each family the splitting of one record is changed (exactly that record fails); one record is
  removed from the `d_regular f_ge_dv` family (`cover43` fails). The commands and outputs are in `controls/ctl2/`.
- `controls_v2_with_v3.log`: on small test certificates, with `controls/controls_v2.py`: records that use Lemma 3.12
  on an unbounded box or with Psi <= 0, a four-point record checked with the closed formula of Ke et al. away from
  f = d (environment variable `NET4=0`; all runs on the certificate used the default), a record on a box with
  unbounded f whose splitting joins Q without removing the edge ZQ, and a record that needs Lemma 3.11 under an
  earlier version of the checker all fail.
- `cover_controls_cov80.log`: dropped, altered and duplicated records make `cover43` fail.
- `audit_crafted_records.log`: records crafted during an audit of the checker, which an earlier version (version 2)
  accepted and the final version rejects (Section 5.4).

## Proposition 6.1

`bash obstruction/run.sh PYTHON` reproduces `obstruction/out/` in a few seconds on one core (python-flint and g++
needed). `obstruction/tools/obstruction.py` evaluates, in ball arithmetic at w* and w1 with f = d, all 1,422 pairs of
a splitting of the d_regular table and a lemma set (`out/way1_*.txt`), and enumerates the 42,303 combinations of
Proposition 6.1(b) with lower bounds for the length of S+ (`out/way3_*.txt`). `obstruction/tools/ceilpt/` evaluates
the formulas of Ke et al. in double precision at the same points (`out/way2.txt`). `out/summary.txt` has one line per
computation.

## Checks of the proofs

`checks/identities.py` checks with sympy the identities used in Sections 2 and 3 (74 checks, output
`checks/out_identities.txt`). `checks/remark_examples.py` checks the two examples of Remark 3.9 in exact rational
arithmetic (output `checks/out_remark_examples.txt`).

## Source versions

The comments in some source files were edited for this release. `SOURCES.md` lists these files with the SHA-256 of
the version used in the runs, which is the value in the logs, and of the version here. For the C and C++ files, both
versions compile to identical object files; for the Python files, both compile to identical bytecode once docstrings
are removed. The shell scripts in `runs/` refer to the working directory as `$WORK` instead of a path.

## Versions

Version 3 adds the second formal proof (`lean_kernel/`, Section 7.1 of the paper), whose checks all run in the Lean
kernel, and the hash lists of its generated modules; the other files are those of version 2
(doi:10.5281/zenodo.23582438). Version 2 added the first formal proof (`lean/`) and its data files. The certificate files,
the other programs, the logs and the controls are those of version 1 (doi:10.5281/zenodo.23570502).

## Provenance and licences

- `splits/d_regular_splits.txt` and `splits/d_steiner_splits.txt` are the files `certificate/d_*/splits.txt` of
  https://github.com/keyisi2006/Steiner-Ratio at commit 8f19604. `generator/` is derived from the generator in the
  same repository, and `generator/formulas/` and `obstruction/tools/ceilpt/formulas/` contain or extend its formulas.
  These files are under the MIT License, Copyright (c) 2025-2026 Yisi Ke and Yankai Shu; the licence text is in
  `generator/LICENSE_PKU_MIT.txt` and `obstruction/tools/ceilpt/LICENSE_PKU_MIT.txt`.
- `checker/indep43c.c` and `checker/indep43.py` were written from the statements in the paper of Ke et al. and from
  reading their verifier, whose record format they use; they contain no code of that repository. The same holds for
  `obstruction/tools/indep43.py`.
- All other programs, including the Lean files, are under the Apache License 2.0 (`LICENSE`). The certificate files,
  the data files of the formal proofs, the hash lists and the logs are under CC BY 4.0.
