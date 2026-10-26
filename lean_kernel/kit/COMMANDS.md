# Commands of the unit build

Run the commands from `lean_kernel/` after `K=$(pwd)`. `LEAN` is the absolute path of the Lean v4.35.0-rc3 binary, and
`TC` is its `lib/lean` directory. Every `LEAN_PATH` entry is absolute, since Lean runs from other directories. `OUT/lib`
is the output of `tools/build_chain.sh` (checker library and proof chain). `SRC` is a directory for the regenerated unit
sources, and `BUILD`, in `lean_kernel/`, is a directory for the unit build outputs.

The archived lists are in `lean_kernel_lists.tar.xz`, deposited with this release, in the format of `sha256sum`.
`units_source_sha256.txt` lists every unit source, with paths relative to `SRC`. `units_olean_sha256.txt` lists the
`.olean`, `.olean.server` and `.olean.private` file of every unit, with paths relative to `BUILD`.
`aggregators_olean_sha256.txt` lists the same three files of every aggregator, with paths relative to `AGG/build`.
`final_olean_sha256.txt` lists those of the final module, with paths relative to `FINAL`. `AGG` and `FINAL` are the
directories used in `assembly/README.md`.

Data. The case data are the archives `data_C1.tar.xz` to `data_C4.tar.xz` deposited with this release, and
`lean/README.md` says where to put them. Their SHA-256 values are in `lean/evidence/data_archives.txt`, and those of the
shard streams are in `lean/evidence/data_shards_sha256.txt`. Each archive unpacks to `s/skel.txt`, `s/ranges.txt` and
`s/shard_NNNNN.txt`.

Checker library alone. This builds the same files as `tools/build_chain.sh`:

    LEAN=$LEAN LEAN_PATH=$TC:$K/OUT/lib LIBOPTS="-DautoImplicit=false -DElab.async=false" \
      python3 kit/libbuild_v2.py checker OUT/lib 4 S43Walk.WalkK2

Job maps. The command below reproduces `kit/jobmap2_Ck.tsv`. NB is the number of box coordinates of the case (6, 7, 6, 8
for C1 to C4). The target number of records per unit is 1,200. A unit holds whole jobs of one shard and closes before
the job that would take it past 1,200 records.

    python3 kit/jobmap43k_v2.py DATA_DIR Ck NB 1200 jobmap2_Ck.tsv

Unit sources of one shard, or of its units U0 to U1, with a self-check. The generator replays, in Python, the walk that
each unit's theorem `walk` makes the kernel check. `S43Walk.WalkK2` is the depth-first replay of the case's subdivision
tree over the unit's slice of the code stream, from its start stack to its end stack:

    python3 kit/gen43k_shard_v4.py DATA_DIR Ck SHARD kit/jobmap2_Ck.tsv SRC [--units U0-U1] --selfcheck

This writes `SRC/S43U/Ck/S<shard:04d>/U<unit:06d>.lean` and `SRC/jobs.tsv`. `SRC/jobs.tsv` has one row per unit, and its
seventh column is the SHA-256 of the source. In `SRC`, `sha256sum -c --ignore-missing units_source_sha256.txt` checks
the regenerated sources against the archived list.

Unit build, run from `SRC` with one thread. The outputs go to `BUILD`:

    mkdir -p $K/BUILD/S43U/Ck/S<shard>
    LEAN_NUM_THREADS=1 LEAN_PATH=$TC:$K/OUT/lib $LEAN -DElab.async=false -j1 --root=. \
      -o $K/BUILD/S43U/Ck/S<shard>/U<unit>.olean S43U/Ck/S<shard>/U<unit>.lean

In `BUILD`, `sha256sum -c --ignore-missing units_olean_sha256.txt` checks the outputs `.olean`, `.olean.server` and
`.olean.private`. Their bytes depend only on the source and the relative module path. Each unit exports exactly three
public declarations: `startSt`, `endSt` and `unit : S43K.UnitClaim st fval nb startSt endSt`.
