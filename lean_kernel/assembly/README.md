# Aggregators, final file and gate

Run the commands from `lean_kernel/` after `K=$(pwd)`. `LEAN` is the absolute path of the Lean v4.35.0-rc3 binary, and
`TC` is the absolute path of its `lib/lean` directory. `PKGS` is the lake packages directory, as for
`tools/build_chain.sh`. `<packages>` is the colon-separated list of the absolute paths of the directories
`PKGS/*/.lake/build/lib/lean`. Lean runs from other directories in steps 3 to 5, so every `LEAN_PATH` entry is absolute.
`OUT/lib` is the output of `tools/build_chain.sh`, and `BUILD` is the directory holding the unit `.olean` files. The
units of a case are in stream order, the order of their slices in the case's code stream (unit index 0, 1, ... of the
job maps). A unit's start and end stacks are the explicit stacks of pending boxes before and after its slice. They are
exported as `startSt` and `endSt`. `kit/COMMANDS.md` describes `BUILD` and these exports.

1. Map of the units, in stream order (case number, unit index, module, its start and end stacks):

       for k in 1 2 3 4; do awk -F'\t' 'NR > 1 { m = sprintf("S43U.%s.S%04d.U%06d", $1, $2, $3);
         print substr($1, 2) "\t" $3 "\t" m "\t" m ".startSt\t" m ".endSt" }' kit/jobmap2_C$k.tsv; done > map.tsv

2. Aggregator sources. Each aggregator has 64 children, and each case has one `Root` module, stating
   `S43K.ChainK k (S43K.rootStackK k) []`:

       python3 assembly/gen_agg_v4.py --map map.tsv --out AGG --fanin 64 --unit-olean-root BUILD \
         --chain-fmt 'S43K.ChainK {k} {a} {b}' --trans S43K.chainK_trans --of-unit S43K.chainK_of_unit \
         --lib-import S43KChainU --root-fmt '(S43K.rootStackK {k})' --root-import S43KChainU --end-fmt '[]'

3. Aggregator build, level by level. Each module is compiled with `lean --setup`, so that only the public `.olean` of
   its children is loaded:

       AGG_LEAN=$LEAN AGG_LEAN_PATH=$K/OUT/lib:$TC bash assembly/build_agg_v2.sh AGG

   In `AGG/build`, `sha256sum -c aggregators_olean_sha256.txt` checks the outputs against the archived list (see
   `kit/COMMANDS.md`).

4. The final file. It is compiled from its source root `final/`, with the output in `FINAL`:

       mkdir -p FINAL && (cd final && LEAN_PATH=$TC:$K/OUT/lib:$K/AGG/build:<packages> \
         $LEAN -DautoImplicit=false -DElab.async=false -j1 --root=. -o $K/FINAL/S43KFinal.olean S43KFinal.lean)

   In `FINAL`, `sha256sum -c final_olean_sha256.txt` checks its three output files.

5. The gate. It checks that the final theorems are theorems whose types are those of the module copy
   `chain/n2m/S43/Statements.lean`, the module form of the statement file `lean/S43/Statements.lean`. It also checks
   that their axioms are within `propext`, `Classical.choice`, `Quot.sound`, that the module copy equals the statement
   file up to the module header, and that every `S43` constant the two statements depend on has the same type and value
   as in the plain (non-module) build of `lean/`. The gate reads the statement file from a directory with its own
   `SHA256SUMS`. Make one from `lean/` and check the file against the repository's top-level `SHA256SUMS` (entry
   `lean/S43/Statements.lean`), whose SHA-256 is `ab138a5156b4181e5634d691ffa5e2c9ea31c40f72a298389f69d1e5b1be722f`:

       mkdir -p STMT/S43 && cp ../lean/S43/Statements.lean STMT/S43/
       (cd STMT && sha256sum S43/Statements.lean > SHA256SUMS && cat SHA256SUMS)
       AXG_LEAN=$LEAN AXG_LEAN_PATH=$TC:$K/FINAL:$K/AGG/build:$K/OUT/lib:<packages> \
       AXG_FROZEN=STMT AXG_STMT_SHA=ab138a5156b4181e5634d691ffa5e2c9ea31c40f72a298389f69d1e5b1be722f \
       AXG_FROZEN_LEAN_PATH=$TC:$K/../lean/.lake/build/lib/lean:<packages> \
       AXG_STMT_COPY=chain/n2m/S43/Statements.lean bash assembly/axgate_v5.sh GATE

   The verdict is in `GATE/axgate_verdict.txt`, and any problems are listed in `GATE/axgate_problems.txt`.
