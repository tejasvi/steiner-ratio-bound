# Lean proof of "The Steiner ratio is at least 0.8564"

This Lean 4 project proves Theorem 1.1 of the paper from the hypotheses (H1)-(H3) of its Section 7: the bounds for
the hidden terminals, the domains of the configurations, and the splitting framework of Du and Hwang, which includes
the case of sets of at most four points, the check that the entries of the tables are splittings and the induction on
the number of points. It uses Lean v4.35.0-rc3 and Mathlib at commit c55e6e786f49471c72fbddbec5415808896aec1e (tag
v4.35.0-rc3); `lake-manifest.json` pins every dependency.

## The two theorems

`S43/Statements.lean` states the two theorems with placeholder proofs (`sorry`), together with the definitions they
use, except the tables of splittings and the numbering of the vertices. Those come from `S43Core/Geom.lean` (`Split`,
`Ids`, `idsReg`, `idsSt`, `edgeKey`) and `S43Core/Splits.lean` (`parseSplits` and the two tables, embedded as text),
so these two files are part of the statements. `parseSplits` turns a malformed line into an empty entry; every one of
the 1,576 lines of the two tables parses (`evidence/release_checks/parse_check.txt`). The statements were reviewed against the paper in versions of these three files that differ from the ones
here only in their comments (SHA-256: `S43/Statements.lean`
1f96c6bfb4b408f36210e075e5d6925ad1c92d808b003a204feb80c4e3301cef, `S43Core/Geom.lean`
e49e38fb3cdf0890b7be46663818cc66f20dad62453a58d136e8352cdd74e62c, `S43Core/Splits.lean`
e22989b1eb56955b6f93d4fff0900eaa6f5dea1a46656da1262b5bc2284fd12f; see also `SOURCES.md`). `S43Final.lean` proves theorems of the same types
and checks this with two `example ... := rfl` lines. A build therefore reports the placeholders of
`S43/Statements.lean`, but the proved theorems do not use `sorryAx` (`evidence/axioms.txt`).

- `S43.Final.certificate`, without hypotheses: for each of the two configuration types (`Fam.reg` = d_regular,
  `Fam.st` = d_steiner) and each parameter `w` of its domain, some entry of the table and some lemma set `L <= 8`
  satisfy `certifies`: every edge of t* at a hidden terminal has a bound of the lemma set whose condition holds at
  `w`, and rho L(t*) + L_SMT(S+) - L(S-) <= 0 at rho = 2141/2500. Here the edges of t* at the hidden terminals are
  priced by these bounds, and L_SMT(S+) is the length of a Steiner minimal tree for the points that S+ joins.
- `S43.Final.steiner_ratio_ge`: (2141/2500) * mstLength P <= steinerLength P for every finite set `P` of complex
  numbers, for every relation `Real` with `LemmaLayer Real`. `mstLength` and `steinerLength` are infima of the total
  lengths of finite sets of segments that connect `P`, with endpoints in `P` for the first and arbitrary endpoints for
  the second.

The relation is named `Real` (it has nothing to do with the real numbers). `Real F w X Y` stands for "some full
Steiner minimal tree, placed as in Lemma 2.5 of the paper, contains a configuration of type `F` with parameter `w`
whose hidden terminals are `X` and `Y`". In these files the hidden terminals E and F of the paper are called `X` and
`Y`, and its Steiner points X, Y, Z are called `s`, `r`, `P`. The hypotheses bundled in `LemmaLayer` are:

| hypothesis | content | in the paper |
|---|---|---|
| `HTrap` | each bound of `lemmaBound` holds whenever its condition does | Lemmas 3.4-3.8, 3.11 and 3.12 |
| `HDomain` | the parameter of a configuration lies in the domain of its type | Lemma 2.5 |
| `HDuHwang` | if every configuration has an entry of the table with cost at most 0, the edges at the hidden terminals counted with their true lengths, then rho L_MST <= L_SMT for every finite set | Lemmas 2.2-2.5, Sections 2.6 and 3.1, the check of Section 4.1 and the transcription of the tables into numeric form (both by programs), the induction of Section 5.5 |

## Files

| path | contents |
|---|---|
| `S43/Statements.lean` | the statements and their definitions (see above) |
| `S43/IntervalSound.lean`, `S43/Sound/` | the proof that the checking program is correct: enclosures of the interval operations, the explicit networks and their convexity, boxes from their vertices, unbounded sides, the check of a box, the tree walks, the four families, and the deduction of the main theorem |
| `S43Core/` | the checking program, in core Lean and compiled: dyadic intervals (`Interval`), the configurations and the lemma bounds (`Geom`, `Vertex`), the tables (`Splits`), the check of one box (`Check`) and the replay of a tree (`Tree`) |
| `S43Data/` | `Loader.lean`, whose command `load_cert_chunk` defines a string constant from a data file after checking its 64-bit FNV-1a hash and that it has no byte of value 128 or more; for each family `Ck`, the skeleton `Skel.lean`, the shard modules `ShardNNNNN.lean` (one `native_decide` theorem each) and `Case.lean` |
| `S43Pilot/` | a pilot (`P80`) and three controls that must fail (`CtlRho`, `CtlTamper`, `CtlDrop`) |
| `data/` | the numeric tables of splittings and the data of the pilot and of the controls; the data of the four families go to `data/C1/s` to `data/C4/s` |
| `tools/` | `make_data.sh` and the programs it runs, which produce the data from the certificate files |
| `evidence/` | `axioms.txt` (output of `evidence/Axioms.lean`), checksums of the data and of the tools, the job ranges of the shards, and `release_checks/` (see below) |

The checker evaluates a vertex with `evalVertexN` of `S43Core/Vertex.lean` (called in `Check.lean`). Some functions of
`S43Core/Geom.lean` are not used by it: `coords`, `smt3` (the closed formula for three points), `psiY2Pos`,
`evalVertex` and `net4`, the branch of `lemmaEntry` for the key `Y` (the checker uses its own, `lemmaEntryN`), and the
branches for the closed four-point formulas (keys `ADQR` and `BDQR`), which `edgeKey` never returns. `S43Core/Main.lean` and `S43Core/TreeMain.lean` are command-line tools that run the
same checks on record files and on code-stream files; the proof does not use them.

The four families are C1 = d_regular with f >= d, C2 = d_steiner with f >= d (checked with f = d, Lemma 4.3),
C3 = d_regular with f <= d and C4 = d_steiner with f <= d.

| family | leaves (= records) | jobs | shards | bytes of data (skeleton, shards, ranges) |
|---|---|---|---|---|
| C1 | 10,376,823 | 12,507 | 6 | 41,519,887 |
| C2 | 12,696,761 | 17,542 | 11 | 50,804,744 |
| C3 | 95,569,010 | 102,728 | 28 | 382,379,482 |
| C4 | 436,460,311 | 515,548 | 437 | 1,746,368,603 |
| total | 555,102,905 | 648,325 | 482 | |

## Data

The data of a family are its tree, written as a stream of codes in depth-first order: an internal box that is split
along coordinate k is the character `'!' + k`, and a leaf is `'p' + L` (`'y'` for lemma set -1) followed by its
splitting number in two base-64 digits. The checking program recomputes every box from the root boxes and the codes,
so the data need not be trusted; a malformed stream makes the check fail. The top levels of each tree form the
skeleton (`skel.txt`), and the subtrees below it are jobs of at most 2,000 leaves, grouped into shards
(`shard_NNNNN.txt`; `ranges.txt` gives the first job, the number of jobs, the leaves and the bytes of each shard).

The data of the four families are archived with the paper's supplementary files (doi:10.5281/zenodo.23582438) as
`data_C1.tar.xz` to `data_C4.tar.xz`. Each unpacks to a directory `s/`, so in this directory

```
for c in C1 C2 C3 C4; do mkdir -p data/$c && tar -xJf data_$c.tar.xz -C data/$c; done
```

puts the files in place. The checksums of the archives are in `MANIFEST.txt` at the top of the repository, and those
of the files they contain in `evidence/data_sums.txt` and `evidence/data_shards_sha256.txt`. The data can also be
regenerated from the certificate files: after `xz -d` of the eight certificate files into a directory `CERT_DIR`,
`sh tools/make_data.sh CERT_DIR` (gcc and python3 needed) runs `tree43c.c`, which writes the code stream of a tree from a
record file and its tree file and compares every leaf box with its record, `split43.c`, which cuts the stream into
the skeleton and the shards, and `gen_lean43c.py`, which writes the Lean modules of each family. On the data of the
paper it reproduces `data/Ck/s` and the 490 modules of `S43Data/C1` to `S43Data/C4` byte for byte
(`evidence/release_checks/make_data_compare.txt`); it ran in 247 seconds. The skeleton and shard modules
name `tools/gen_lean43.py` as their generator, the original name of `gen_lean43c.py`; the two versions write identical
skeleton and shard modules, and `gen_lean43c.py` writes a different `Case.lean`.

## Building

With elan installed, in this directory:

```
lake exe cache get
lake build S43.Sound.MainProof S43.Sound.Data S43Pilot.P80.Case
```

This builds the checking program, its correctness proof and the pilot: the complete certificate at rho = 4/5 of
d_regular with f >= d (427 records, 74 jobs, 4 shards), which gives the theorem `S43Pilot.P80.case`. With Mathlib
already built it took 154 seconds with `LEAN_NUM_THREADS=8` (`evidence/release_checks/build_time.txt`). The controls
must fail; each of their shard modules was built separately (`evidence/release_checks/controls.txt` and
`control_logs/`): with the pilot data checked at rho = 9/10 (`CtlRho`) all four shards fail; with one leaf given lemma
set -1 (`CtlTamper`) shard 1 fails and shards 0, 2 and 3 pass; with the last leaf of shard 3 removed (`CtlDrop`)
shard 3 fails and shards 0-2 pass. In each failing shard `native_decide` evaluates the check to false.

For the full proof, put the data of the four families in place, then run

```
lake build S43Final
lake env lean evidence/Axioms.lean
```

The second command prints the axioms of the two theorems; `lake build S43Data.C1.Case` builds the smallest family
alone. The full build ran on two machines with 384 hardware threads and 708 GiB of memory each
(`evidence/release_checks/machines.txt`), with `LEAN_NUM_THREADS=20`, so that at most 20 shard modules were built at a
time; each Lean process checked the jobs of its shard in parallel tasks, and the machines ran at full load. One
machine built the families C1-C3 and the shards 0-194 of C4 in 16,114 seconds, the other the shards 195-436 of C4 in
14,924 seconds. The build outputs of the second machine were copied to the first, where `lake build --no-build`
accepted them without rebuilding, and the remaining modules then built in 10 seconds. The kernel checked the
declarations of each shard module on the machine that built it; the outputs of the second machine were not checked
again on the first (for example with lean4checker).

## What is trusted

The shard theorems, three facts about each family (`mono`, `skelSome`, `skelN`) and two facts about the tables
(`S43.Final.sizes_st`, `S43.Final.sizes_reg`) are proved by `native_decide`, which compiles the checks and runs them.
Each such theorem adds one axiom (`<name>._native.native_decide.ax_1`) stating that the compiled check returned true:
496 for `S43.Final.steiner_ratio_ge` and 494 for `S43.Final.certificate`, besides `propext`, `Classical.choice` and
`Quot.sound`. Trusting these axioms means trusting, in addition to Lean's kernel, the Lean compiler and its
interpreter, the C compiler, the Lean runtime and the compiled core-library functions that the checks call. The
checking program uses floating point only to choose the Steiner points of the explicit networks, which are then
rounded to multiples of 2^-40; the correctness proof holds for every choice. The data enter only through the
constants defined by `load_cert_chunk`, and the proof does not depend on their content.

## Checks of this release

`evidence/release_checks/` holds checks run on a clean copy of the files as published: the build of the pilot, the
controls, the regeneration of the data from the published certificate files (whose decompressed checksums equal those
of the certificate's `MANIFEST.txt`), and the description of the machines of the full run. The comments of some files
were edited for the release; the build of the full proof used the earlier versions, whose declarations and axioms are
the same (`SOURCES.md` lists these files with both checksums).
