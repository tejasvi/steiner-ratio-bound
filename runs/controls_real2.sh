#!/bin/bash
# on the run machine after the v3 passes: must-fail controls (checker v3) on the real certificates -> ${WORK:?}/controls_real2.log
#  (1) just-above claims 2142/2500 and 4283/5000 on the first 2M records of each case (20 chunks of 100k, in parallel): failures
#      must appear;
#  (2) tampered record: in a copy of the first 100k records of each case, one record's split id is changed (the first record from
#      index 1000 on that the checker does not skip and whose changed split fails the vertex test F <= 0 when checked alone);
#      the whole tampered copy must show exactly that one failure, the untouched copy none;
#  (3) coverage tamper on the smallest case (d_regular f_ge_dv): record 5000 dropped -> cover43 must FAIL.
L=${CTL_LOG:-${WORK:?}/controls_real2.log}; T=${WORK:?}/tools; W0=${CTL_DIR:-${WORK:?}/ctl2}; C=$W0/cmds.txt; mkdir -p $W0; : > $L; : > $C
JN=${JA_N:-20}; JC=${JA_CHUNK:-100000}; SL=${SLICE:-100000}   # (small values only for testing the script)
echo "start $(date -u +%FT%TZ) checker $(sha256sum ${WORK:?}/tools/indep43c_v3.c | cut -c1-16) cover $(sha256sum ${WORK:?}/tools/cover43.c | cut -c1-16)" >> $L
cases="d_regular:f_ge_dv:6 d_steiner:f_ge_d:7 d_regular:f_le_d:6 d_steiner:f_le_d:8"
for c in $cases; do
  IFS=: read fam sub nb <<< "$c"; cert=$(ls ${WORK:?}/cert_${fam}_${sub}_0.8564/certificate_rho=*.bin); rs=$((8 + 16 * nb + 8))
  for pq in "2142 2500" "4283 5000"; do
    set -- $pq
    for i in $(seq 0 $((JN - 1))); do echo "$T/indep43c64_v3 $fam $sub $T/splits/$fam.num $cert $1 $2 $((i * JC)) $JC > $W0/ja_${fam}_${sub}_$1_$i.json 2>&1" >> $C; done
  done
  W=$W0/t_${fam}_${sub}; mkdir -p $W; head -c $((rs * SL)) $cert > $W/slice.bin; found=""; nskip=0; nstruct=0; npass=0
  for k in $(seq 1000 3000); do
    m=$(python3 ${WORK:?}/src/tamper2.py $W/slice.bin $W/tampered.bin $fam $sub $k)
    case "$m" in tampered*) ;; *) nskip=$((nskip + 1)); continue ;; esac
    r=$($T/indep43c64_v3 $fam $sub $T/splits/$fam.num $W/tampered.bin 2141 2500 $k 1)
    if echo "$r" | grep -q '"fail": 1,'; then
      if echo "$r" | grep -q 'vertex value not <= 0'; then found="$m"; break; fi
      nstruct=$((nstruct + 1))
    else npass=$((npass + 1)); fi
  done
  echo "tamper $fam $sub: ${found:-NO CANDIDATE FAILED NUMERICALLY} (wanted: the changed split fails the vertex test F <= 0; candidates before it: $nskip skipped by the checker's rules, $nstruct rejected structurally, $npass still valid)" >> $L
  echo "$T/indep43c64_v3 $fam $sub $T/splits/$fam.num $W/slice.bin 2141 2500 0 0 > $W/untouched.json 2>&1" >> $C
  if [ -n "$found" ]; then
    echo "$found" > $W/found.txt
    echo "$T/indep43c64_v3 $fam $sub $T/splits/$fam.num $W/tampered.bin 2141 2500 0 0 > $W/tampered.json 2>&1" >> $C
  fi
done
d=${WORK:?}/cert_d_regular_f_ge_dv_0.8564; cert=$(ls $d/certificate_rho=*.bin); child=$(ls $d/child_rho=*.bin); rs=$((8 + 96 + 8))
head -c $((rs * 5000)) $cert > $W0/cert_drop.bin; tail -c +$((rs * 5001 + 1)) $cert >> $W0/cert_drop.bin
( $T/cover43_64 $W0/cert_drop.bin $child 6 > $W0/cover_drop.out 2>&1; echo "rc $?" >> $W0/cover_drop.out ) &
cp=$!
xargs -P 95 -I{} sh -c '{}' < $C
wait $cp
python3 - $W0 $JN $JC >> $L <<'PY'
import sys, json, glob, os
w = sys.argv[1]; JN, JC = int(sys.argv[2]), int(sys.argv[3]); bad = 0
for fam, sub in [('d_regular', 'f_ge_dv'), ('d_steiner', 'f_ge_d'), ('d_regular', 'f_le_d'), ('d_steiner', 'f_le_d')]:
    for p in (2142, 4283):
        t = {'count': 0, 'fail': 0, 'ok': 0}; ex = None; n = 0
        for i in range(JN):
            j = json.loads(open(f'{w}/ja_{fam}_{sub}_{p}_{i}.json').read()); n += 1
            for k in t: t[k] += j[k]
            if ex is None and j['fails']: ex = j['fails'][0]
        q = 2500 if p == 2142 else 5000
        v = 'AS EXPECTED' if t['fail'] > 0 and t['count'] == JN * JC and n == JN else 'NOT AS EXPECTED'; bad += v != 'AS EXPECTED'
        print(f'just-above {fam} {sub} rho={p}/{q} first {JN * JC} records: {t} first failure {ex} -> {v}')
    u = json.loads(open(f'{w}/t_{fam}_{sub}/untouched.json').read())
    tt = json.loads(open(f'{w}/t_{fam}_{sub}/tampered.json').read()) if os.path.exists(f'{w}/t_{fam}_{sub}/tampered.json') else None
    fk = int(open(f'{w}/t_{fam}_{sub}/found.txt').read().split()[1]) if os.path.exists(f'{w}/t_{fam}_{sub}/found.txt') else -1
    v = ('AS EXPECTED' if u['fail'] == 0 and tt and tt['fail'] == 1 and tt['ok'] == u['ok'] - 1 and tt['fails'][0]['rec'] == fk
         and tt['fails'][0]['why'] == 'vertex value not <= 0' else 'NOT AS EXPECTED'); bad += v != 'AS EXPECTED'
    print(f"tamper slice {fam} {sub}: untouched fail {u['fail']} ok {u['ok']}; tampered fail {tt and tt['fail']} ok {tt and tt['ok']} fails {tt and tt['fails']} -> {v}")
c = open(f'{w}/cover_drop.out').read().strip().splitlines()
v = 'AS EXPECTED' if any('FAIL' in x for x in c) and not any(x.startswith('OK COVER') for x in c) else 'NOT AS EXPECTED'; bad += v != 'AS EXPECTED'
print('cover43 d_regular f_ge_dv with record 5000 dropped:', ' | '.join(c[-3:]), '->', v)
print('CONTROLS SUMMARY:', 'ALL AS EXPECTED' if bad == 0 else f'{bad} NOT AS EXPECTED')
PY
echo "CONTROLS DONE $(date -u +%FT%TZ)" >> $L
