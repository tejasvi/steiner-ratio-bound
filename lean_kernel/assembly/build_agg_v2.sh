#!/bin/bash
# build_agg_v2.sh: builds AGGDIR/build_order.tsv level by level;
# v2 = v1 + `lean --setup=AGGDIR/setup/<module>.json` per module (gen_agg_v3.py: children by public .olean only) + an
# empty or missing output olean counts as a failure even at rc 0.
# usage: bash build_agg_v2.sh AGGDIR
# env: AGG_LEAN       lean binary (required)
#      AGG_LEAN_PATH  roots with the unit oleans and the kit (toolchain lib, S43CoreK/S43Walk, K3 glue) (required);
#                     AGGDIR/build is prepended
#      AGG_NPAR       modules built in parallel within one level (default 1)
#      AGG_TIMEOUT    seconds per module (default 7200)
#      AGG_MAXN       stop after building this many modules in this call (default 0 = no limit; for batched runs)
#      AGG_MEMG       optional per-module memory cap in GB (systemd-run --scope MemoryMax; needs root)
# Per module: cd AGGDIR/src && LEAN_PATH=AGGDIR/build:$AGG_LEAN_PATH lean -DElab.async=false -j1 --root=. -o AGGDIR/build/<path>.olean <path>.lean
# Logs AGGDIR/logs/<module>.log, times AGGDIR/times.tsv ("module rc wall_s peak_rss_kB level"), command lines
# AGGDIR/cmdlines.txt. A module with an rc-0 line in times.tsv and its olean present is skipped (resume). Stops after the
# first level with a failure. Exit 0 iff every module of build_order.tsv has built.
set -u
D=$(cd "${1:?usage: build_agg_v2.sh AGGDIR}" && pwd)
LEAN=${AGG_LEAN:?AGG_LEAN not set}; LPB=${AGG_LEAN_PATH:?AGG_LEAN_PATH not set}
NPAR=${AGG_NPAR:-1}; TMO=${AGG_TIMEOUT:-7200}; MAXN=${AGG_MAXN:-0}
H=$(cd "$(dirname "$0")" && pwd); RT=$H/agg/rtime_v1.py
[ -f "$RT" ] || { echo "missing $RT"; exit 2; }
mkdir -p "$D/build" "$D/logs"; touch "$D/times.tsv" "$D/times.tsv.part" "$D/cmdlines.txt"
export LEAN LPB TMO D RT
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
one() {  # $1 = level, $2 = module
  local lvl=$1 m=$2 p cmd
  p=$(echo "$m" | tr . /)
  mkdir -p "$D/build/$(dirname "$p")"
  cmd="$LEAN --setup=$D/setup/$m.json -DElab.async=false -j1 --root=. -o $D/build/$p.olean $p.lean"
  [ -n "${AGG_MEMG:-}" ] && cmd="systemd-run --scope --quiet --collect -p MemoryMax=${AGG_MEMG}G -p MemorySwapMax=0 -- $cmd"
  echo "$m :: cd $D/src && LEAN_PATH=$D/build:$LPB timeout -k 10 $TMO $cmd" >> "$D/cmdlines.txt"
  [ -f "$D/setup/$m.json" ] || { echo "$m 97 0 0 L$lvl" >> "$D/times.tsv"; echo "no setup json" > "$D/logs/$m.log"; return 1; }
  (cd "$D/src" && LEAN_PATH="$D/build:$LPB" python3 -I "$RT" "$D/times.tsv.part" "$m" "L$lvl" timeout -k 10 "$TMO" $cmd > "$D/logs/$m.log" 2>&1)
  local rc=$?
  # an rc-0 run that left no or an empty olean is a failure (98)
  if [ $rc = 0 ] && [ ! -s "$D/build/$p.olean" ]; then rc=98; fi
  awk -v m="$m" -v r=$rc '$1 == m {$2 = (r == 98 ? 98 : $2)} $1 == m' "$D/times.tsv.part" | tail -1 >> "$D/times.tsv"
}
export -f one
built=0
for lvl in $(cut -f1 "$D/build_order.tsv" | sort -n -u); do
  todo=$(awk -F'\t' -v L="$lvl" '$1 == L {print $2}' "$D/build_order.tsv" | while read -r m; do
    p=$(echo "$m" | tr . /)
    if awk -v m="$m" '$1 == m && $2 == 0 {f = 1} END {exit !f}' "$D/times.tsv" && [ -s "$D/build/$p.olean" ]; then continue; fi
    echo "$m"; done)
  [ -z "$todo" ] && continue
  if [ "$MAXN" -gt 0 ]; then
    left=$((MAXN - built)); [ "$left" -le 0 ] && { echo "batch limit reached ($built built)"; exit 3; }
    todo=$(echo "$todo" | head -n "$left")
  fi
  n=$(echo "$todo" | wc -l)
  echo "$todo" | xargs -P "$NPAR" -I{} bash -c "one $lvl {}"
  built=$((built + n))
  nfail=$(echo "$todo" | while read -r m; do awk -v m="$m" '$1 == m {rc = $2} END {if (rc != 0) print m}' "$D/times.tsv"; done | wc -l)
  echo "level $lvl: built $n, failed $nfail"
  [ "$nfail" = 0 ] || { echo "FAIL at level $lvl"; exit 1; }
  if [ "$MAXN" -gt 0 ] && [ "$built" -ge "$MAXN" ]; then
    rest=$(awk -F'\t' '{print $2}' "$D/build_order.tsv" | while read -r m; do
      p=$(echo "$m" | tr . /); awk -v m="$m" '$1 == m && $2 == 0 {f = 1} END {exit !f}' "$D/times.tsv" && [ -s "$D/build/$p.olean" ] || echo "$m"; done | wc -l)
    [ "$rest" = 0 ] && { echo "ALL BUILT"; exit 0; }
    echo "batch limit reached ($built built, $rest left)"; exit 3
  fi
done
echo "ALL BUILT"
