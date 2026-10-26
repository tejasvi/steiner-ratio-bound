# Kernel-only proof

This directory proves the same two theorems as `lean/`, namely `certificate` and `steiner_ratio_ge` of
`lean/S43/Statements.lean` (the Steiner ratio is at least 2141/2500, given the lemma layer), with no native code. There
is no `native_decide`, and the axioms of both final theorems are exactly `propext`, `Classical.choice` and `Quot.sound`.
The lemma layer is the hypothesis `H : LemmaLayer Real` of `steiner_ratio_ge`. It bundles `HTrap`, `HDomain` and
`HDuHwang`, all defined in that file. The toolchain and libraries are the same as for `lean/` (Lean v4.35.0-rc3, Mathlib
at the commit in `lean/lake-manifest.json`).

## How the proof is organised

The certificate's 555,102,905 records are checked by Lean's kernel. A checker written for kernel evaluation (`checker/`)
uses interval arithmetic on biased natural numbers and decides every record with `decide +kernel`. The records sit in
455,318 generated unit modules (C1 9,066, C2 10,737, C3 76,782, C4 358,733). Each unit module also replays its slice of
the case's subdivision tree. Aggregator modules chain the units of each case from the full box to the empty stack. The
proof chain (`chain/src/`) shows that such a chain gives `CaseOK` (from `lean/`) for the case, and the final assembly in
`lean/` then gives the two theorems.

Layers of `chain/src/`:
- K0 (`K0Lemmas`, `K0Lits`, `K0Bridge`, `KData`): the statement's split lists equal explicit literals. The split-table
  facts `monoCheck`, `sizeCheck` are decided by the kernel.
- K1 (`DNSim`, `DNBound`, `OpLayer`, `GeomEB` to `GeomEB7`, `GeomLem`, `VertexSoundK`): soundness of the vertex
  evaluation. Every value is statically bounded, so the natural-number subtractions never truncate.
- K2 (`RecordK`, `SplitsGlue`, `SplitsGlue2`): soundness of the record check.
- K3 (`WalkSoundK`): the walk covers the case domain. A unit's claim transfers coverage from its start stack to its end
  stack.
- K4 (`WalkSoundK`, `MainKTemplate`, `MainKRoot`): the case theorem and the main theorem from the four case roots.
- `S43KChainU` (the aggregators' chain predicate) and `AggLibK` (the final theorems from the four roots).

`chain/n2m/` holds module-form copies of the 25 files of `lean/` that the chain imports. Each is the file of `lean/`
with `module`, `public import`, `@[expose] public section` and a closing `end` added by `tools/to_module_v2.py`.
`final/` holds the final file. It applies the chain to the four case roots and checks the types of the two theorems
against the statement file.

## Building the checker and the proof chain

    (cd ../lean && lake build)        # provides Mathlib and the other packages under ../lean/.lake/packages
    LEAN=<path to lean v4.35.0-rc3> PKGS=../lean/.lake/packages bash tools/build_chain.sh OUT

This compiles the 9 checker modules and the 49 chain modules one at a time and prints the axioms of the chain's main
theorems. Peak memory is about 21 GB, for `SplitsGlue`. Each module is compiled from its source root with `--root`, so
the `.olean` files do not depend on the location of the tree.

## Units, aggregators and the final file

`kit/COMMANDS.md` gives the commands for the units, and `assembly/README.md` those for the aggregators, the final file
and the gate. The gate is step 5 of `assembly/README.md`, the check of the final theorems' types, axioms and statement
constants. The unit sources are not shipped. `kit/gen43k_shard_v4.py` regenerates them from the data archives deposited
with this release (`data_C1.tar.xz` to `data_C4.tar.xz`, see `lean/README.md`) and from the job maps
`kit/jobmap2_C1.tsv` to `kit/jobmap2_C4.tsv`. The archive `lean_kernel_lists.tar.xz`, also deposited with this release,
gives the SHA-256 of every unit source. It also gives the SHA-256 of the three output files (`.olean`, `.olean.server`,
`.olean.private`) of every unit, every aggregator and the final module, so a regeneration can be checked byte for byte.

## Edited files

The proof was built from versions of some files that differ from the ones here only in comments, apart from one code
edit. `SOURCES.md` lists these files with both SHA-256 values, the code edit and the checks that were made. Of the
hashes in `lean_kernel_lists.tar.xz`, only the final module's hashes are affected. Because the module comment was
edited, the `.olean.server` and `.olean.private` files compiled from `final/S43KFinal.lean` here differ from the
corresponding files of the build of the proof. The module's `.olean` file and all its constants and proofs are the same.
`SOURCES.md` gives both sets of SHA-256 values. The archive holds the values for the file here.
