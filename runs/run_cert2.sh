#!/bin/bash
# on the run machine: run_cert2.sh FAMILY SUBCASE RHO NTHREADS -> ${WORK:?}/cert_<fam>_<sub>_<rho>/ (gen43f v2 with the v2 formulas, 64-bit ids)
# SUBCASE: f_le_d (F_VAL 1), f_ge_d (F_VAL 2, f := d), f_ge_dv (F_VAL 3, f a box variable; d_regular only)
fam=$1; sub=$2; rho=$3; nt=$4; W=${WORK:?}/cert_${fam}_${sub}_${rho}
[ -e $W ] && { echo "$W exists"; exit 1; }
mkdir -p $W && cd $W || exit 1
case $fam in d_steiner) FS=1; XF="";; d_regular) FS=0; XF="-DNET4_PREFILTER";; *) echo bad fam; exit 1;; esac
case $sub in f_le_d) FV=1;; f_ge_d) FV=2;; f_ge_dv) FV=3;; *) echo bad sub; exit 1;; esac
cp -r ${WORK:?}/src/${fam}_v2/formulas . && sed "s/RHO_VAL/$rho/" ${WORK:?}/src/gen43f.cpp.tmpl > gen43f.cpp && cp ${WORK:?}/src/LICENSE_PKU_MIT.txt .
echo "start $(date -u +%FT%TZ) host $(hostname) nproc $(nproc) fam $fam sub $sub rho $rho threads $nt src $(sha256sum gen43f.cpp | cut -c1-16) formulas $(cat formulas/* | sha256sum | cut -c1-16)" > gen.log
( time g++ gen43f.cpp -O3 -pthread -Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -std=c++23 -ffast-math -DFAM_STEINER=$FS -DF_VAL=$FV -DID64 $XF -o gen43f ) >> gen.log 2>&1 || { echo "compile failed" >> gen.log; exit 1; }
/usr/bin/time -v -o gen.time ./gen43f $nt > gen.out 2> gen.progress
rc=$?
echo "rc $rc $(date -u +%FT%TZ)" >> gen.log
echo done > DONE
