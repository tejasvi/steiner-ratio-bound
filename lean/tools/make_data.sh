#!/bin/sh
# make_data.sh: the shard data and data modules of the four cases (data/Ck/s, S43Data/Ck/*.lean) from the certificate
# files, byte for byte as in the proof. Run from the package root.
# usage: tools/make_data.sh CERT_DIR
#   CERT_DIR holds the decompressed certificate files under their published names (xz -d of the release record):
#   <family>_<subcase>_certificate.bin and <family>_<subcase>_child.bin for the four cases below.
# Needs gcc and python3; about 100 GB of disk for the decompressed files (they are read in place).
set -e
CERT_DIR=$1
gcc -O2 -o tools/tree43c tools/tree43c.c
gcc -O2 -o tools/split43 tools/split43.c
# case  family     subcase  nb  max leaves per job  min leaves per shard  family (Lean)  fval
while read c fam sub nb J S lf fval; do
  mkdir -p data/$c/s
  tools/tree43c "$CERT_DIR/${fam}_${sub}_certificate.bin" "$CERT_DIR/${fam}_${sub}_child.bin" $nb data/$c/tree.txt
  tools/split43 data/$c/tree.txt $nb $J $S data/$c/s
  python3 tools/gen_lean43c.py . data/$c/s S43Data.$c $lf $fval 2141 2500
done <<CASES
C1 d_regular f_ge_dv 6 2000 2000000 reg 3
C2 d_steiner f_ge_d 7 2000 1200000 st 2
C3 d_regular f_le_d 6 2000 3500000 reg 1
C4 d_steiner f_le_d 8 2000 1000000 st 1
CASES
