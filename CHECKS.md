# Independent checks of the formal proofs

These checks were made after the builds described in `lean/README.md` and `lean_kernel/README.md`. The axioms of both
proofs are listed in `README.md` ("The Lean proofs").

## `lean/` (checks run as compiled code)

The proof was rebuilt on other machines from the same sources and data, re-running every compiled check, and it uses no
axioms besides those listed in `README.md`. The data files were regenerated from the certificate files byte for byte,
every module was replayed in the kernel, and the exported proofs of both theorems were accepted by the kernel checkers
leanchecker, nanoda and lean4lean, with the compiled checks taken as axioms. The released source files differ from those
of this rebuild only in comments.

## `lean_kernel/` (all checks run in the kernel)

Every one of the 455,318 unit modules was regenerated from the data files and compiled with the same command, so that
the kernel checked every record once more. All three compiled files of each unit module are byte-identical to those of
the first build, as are the 36,195 files of the aggregator modules and the 5 files of the final module, rebuilt from
these units. A walk through all the constants that the two final theorems use finds only the axioms listed in
`README.md` and no use of native code. The kernel replayed every aggregator module and the final module. Exports of the
module that chains the units, of the module that reads the tables and of four small units were accepted by Lean's
kernel through leanchecker and by two independent implementations of the kernel, lean4lean and nanoda. Deliberately
altered modules were rejected.
