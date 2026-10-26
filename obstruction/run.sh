#!/bin/bash
# run.sh PYTHON : reproduces out/ (one core, about 1 minute): ways 1 and 3 in arb (obstruction.py), way 2 in double (ceilpt.cpp)
set -e
PY=${1:-python3}; H=$(cd "$(dirname "$0")" && pwd); mkdir -p "$H/out"
cd "$H/tools" && "$PY" -I -B obstruction.py "$H/out" > "$H/out/summary.txt"
cd "$H/tools/ceilpt" && g++ ceilpt.cpp -O2 -std=c++23 -DFAM_STEINER=0 -DF_VAL=2 -o ceilpt 2> /dev/null
./ceilpt 1.3656 1.10927 0.365604 1 0.171605 1.34514 1.07421 0.347656 1.00391 0.167969 > "$H/out/way2.txt"
rm -f ceilpt
cat "$H/out/summary.txt" "$H/out/way2.txt" | grep -E "^(wstar|w1|point)"
