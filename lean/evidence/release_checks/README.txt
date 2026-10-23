Checks run on a clean copy of this package (machine with 384 hardware threads, Mathlib v4.35.0-rc3 already built):
- build_time.txt, build.log: lake build S43.Sound.MainProof S43.Sound.Data S43Pilot.P80.Case with LEAN_NUM_THREADS=8
- controls.txt, control_logs/: the must-fail controls, one shard module at a time (rho 9/10: all 4 shards fail; tampered leaf: shard 1 fails, shards 0, 2, 3 pass; dropped leaf: shard 3 fails, shards 0-2 pass)
- certificate_files_sha256.txt: the published xz files decompressed, sha256 equal to the certificate MANIFEST
- make_data.log, make_data_compare.txt: tools/make_data.sh on those files; data/Ck/s and the 490 S43Data/Ck modules equal the shipped ones byte for byte
- machines.txt: thread and memory counts of the run machines, Lean/Lake versions, and the parallelism settings of the full run
- ../data_archives.txt: the deposited shard-data archives (sizes, sha256, md5) and the tar packing options
- ParseAll.lean, parse_check.txt: every line of the two split tables parses (no line becomes the empty default entry)
