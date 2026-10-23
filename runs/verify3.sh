#!/bin/bash
# on the run machine: verify3.sh (checker v3; cover43 is not re-run: it does not depend on the record checker) FAMILY SUBCASE DIR RHO_P RHO_Q NPROC -> DIR/verify3/ (indep43c64_v3 in chunks of 500k records, then a summary)
fam=$1; sub=$2; d=$3; P=$4; Q=$5; NP=$6; T=${WORK:?}/tools; V=$d/verify3; mkdir -p $V
cert=$(ls $d/certificate_rho=*.bin); child=$(ls $d/child_rho=*.bin)
case "$fam/$sub" in d_steiner/f_le_d) n=8;; d_steiner/f_ge_d) n=7;; d_regular/f_le_d) n=6;; d_regular/f_ge_d) n=5;; d_regular/f_ge_dv) n=6;; *) echo bad; exit 1;; esac
rs=$((8 + 16 * n + 8)); R=$(( $(stat -c %s $cert) / rs ))
echo "start $(date -u +%FT%TZ) $fam $sub rho $P/$Q records $R n $n cert $(sha256sum $cert | cut -c1-16) child $(sha256sum $child | cut -c1-16) indep43c_v3 $(sha256sum $T/indep43c_v3.c | cut -c1-16) cover43 $(sha256sum $T/cover43.c | cut -c1-16) splits $(sha256sum $T/splits/$fam.num | cut -c1-16)" > $V/verify.log
CH=500000
seq 0 $CH $((R - 1)) | xargs -P $NP -I{} sh -c "$T/indep43c64_v3 $fam $sub $T/splits/$fam.num $cert $P $Q {} $CH > $V/chunk_{}.json 2> $V/chunk_{}.err"
wait
python3 - $V $R >> $V/verify.log <<'PY'
import json, glob, sys
V, R = sys.argv[1], int(sys.argv[2]); tot = {"ok": 0, "skip_sym": 0, "skip_sub": 0, "fail": 0, "count": 0}; fails = []; nch = 0; bad = []
for f in sorted(glob.glob(V + "/chunk_*.json")):
    try:
        d = json.loads(open(f).read())
    except Exception:
        bad.append(f); continue
    nch += 1
    for k in tot: tot[k] += d[k]
    fails += d["fails"][:3]
print("chunks", nch, "unreadable", len(bad), "totals", tot, "records", R)
print("first failures", fails[:5])
print("RESULT:", "ALL RECORDS PASS" if tot["fail"] == 0 and tot["count"] == R and not bad else "FAILURES OR MISSING CHUNKS")
PY
