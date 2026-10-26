#!/bin/bash
# build_chain.sh: compile the kernel checker library and the proof chain of lean_kernel/ in dependency order (one module
# at a time), then print the axioms of the chain's main theorems (tools/AxK.lean). Each module is compiled from its source
# root with --root=<root> and a relative path, so the .olean files do not depend on where the tree lies.
# usage: LEAN=<lean v4.35.0-rc3 binary> PKGS=<lake packages dir holding mathlib, batteries, ...> bash tools/build_chain.sh OUT
#   (PKGS: e.g. the .lake/packages of the lean/ project after `lake build` there)
# Output: OUT/lib (the .olean files), OUT/logs, OUT/LIB_SHA256SUMS.
set -u -o pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
OUT=${1:?usage: LEAN=... PKGS=... bash tools/build_chain.sh OUT}
LEAN=${LEAN:?set LEAN to the lean binary}; PKGS=${PKGS:?set PKGS to the lake packages dir}
# absolute paths, since lean runs from each source root
case $LEAN in */*) ;; *) LEAN=$(command -v "$LEAN") || { echo "not found: lean"; exit 9; } ;; esac
LEAN=$(cd "$(dirname "$LEAN")" && pwd)/$(basename "$LEAN"); [ -x "$LEAN" ] || { echo "not executable: $LEAN"; exit 9; }
TCL=$(cd "$(dirname "$LEAN")/../lib/lean" && pwd) || { echo "no ../lib/lean next to $LEAN: use the toolchain's bin/lean"; exit 9; }
PKGS=$(cd "$PKGS" && pwd) || { echo "not a directory: PKGS"; exit 9; }
[ -e "$OUT" ] && { echo "refusing: $OUT exists"; exit 7; }
mkdir -p "$OUT/lib" "$OUT/logs" || exit 8
OUT=$(cd "$OUT" && pwd)
LP=$TCL:$OUT/lib
for d in "$PKGS"/*/.lake/build/lib/lean; do LP=$LP:$d; done
one() {  # $1 source root, $2 module path (A/B/C), $3 non-empty = write the .olean
  local log="$OUT/logs/${2//\//_}.out"
  mkdir -p "$(dirname "$OUT/lib/$2")"
  ( cd "$1" && LEAN_PATH=$LP "$LEAN" -DautoImplicit=false -DElab.async=false -j1 --root="$1" \
      ${3:+-o "$OUT/lib/$2.olean"} "$2.lean" ) > "$log" 2>&1 || { echo "FAILED: $2"; head -n 20 "$log"; exit 1; }
  echo "ok $2"
}
for m in S43CoreK/Ladder S43CoreK/DN S43CoreK/GeomK S43CoreK/VertexK S43CoreK/SplitsK S43CoreK/CheckK \
         S43Walk/SkelK S43Walk/WalkK S43Walk/WalkK2; do
  one "$HERE/checker" "$m" o
done
for x in n2m:S43Core/Interval src:DNSim src:DNBound n2m:S43/IntervalSound n2m:S43Core/Geom src:OpLayer n2m:S43Core/Splits \
    n2m:S43/Statements n2m:S43/Sound/Affine n2m:S43/Sound/Net n2m:S43Core/Vertex n2m:S43/Sound/Enc src:GeomEB src:GeomEB2 \
    src:GeomEB3 n2m:S43/Sound/VertexSound src:GeomEB4 src:GeomEB5 src:GeomEB6 src:GeomEB7 src:GeomLem src:VertexSoundK \
    n2m:S43/Sound/LemmaSound n2m:S43/Sound/EvalSound n2m:S43/Sound/Convex n2m:S43/Sound/Box n2m:S43/Sound/Bump \
    n2m:S43/Sound/Unbounded n2m:S43Core/Check n2m:S43Core/Tree n2m:S43/Sound/Record n2m:S43/Sound/Bridge \
    n2m:S43/Sound/Target src:RecordK n2m:S43/Sound/Walk n2m:S43/Sound/Case src:WalkSoundK src:K0Lemmas src:K0Lits \
    src:K0Bridge src:SplitsGlue src:SplitsGlue2 n2m:S43/Sound/Data src:KData n2m:S43/Sound/MainProof src:MainKTemplate \
    src:MainKRoot src:S43KChainU src:AggLibK; do
  one "$HERE/chain/${x%%:*}" "${x#*:}" o
done
one "$HERE/tools" AxK
grep "axioms" "$OUT/logs/AxK.out"
( cd "$OUT/lib" && find . -type f | LC_ALL=C sort | xargs sha256sum ) > "$OUT/LIB_SHA256SUMS"
echo "BUILD_CHAIN_DONE: $(wc -l < "$OUT/LIB_SHA256SUMS") files"
