#!/bin/bash
# axgate_v5.sh: strict axiom + statement gate for a MODULE-form final.
# v5 = v4 + a strong cone digest: Expr.hash is 32-bit, so each run also writes the
# eta-normalized `toString` of every cone constant's type and value to OUTDIR/cone_{k,f}/ and the comparison requires
# their sha256 to agree on both sides for EVERY constant (raw 32-bit hashes still decide which ones are 'equal up to eta').
# v4 = v3 + (a) the cone compares raw (type, value) hashes and, where they differ, the hashes after a post-order Expr.eta
# on both sides (module-mode derived DecidableEq instances eta-expand a proof argument), reporting
# raw-equal / eta-equal / differ; (b) every problem is reported: counts per category in the verdict line, the full list in
# OUTDIR/axgate_problems.txt (v2/v3 printed only the first 4 problems, which hid 2 differing cone lines behind sorry lines).
# v3 = v2 with the copy text check made exact: the copy must equal one of the two mechanical module forms of the frozen
# file byte for byte (A: tools/to_module_v2.py, as in chain/n2m; B: the module header lines without A's blank lines,
# imports first).
# v2 vs v1: at 455k units a plain check file would load the whole import closure (a non-module importer sets importAll
# on every transitive import), so the kernel-side check is a `module` file; a module cannot import the plain frozen statement,
# so the final is stated against a module-form COPY of S43/Statements.lean, and the gate checks that copy three ways:
# text (= frozen file up to the module header), cone (every S43* constant reachable from each statement theorem has the same
# type and value hashes as in the frozen plain build), and Expr-equality of the final theorems with the copy's ones.
# usage: axgate_v5.sh OUTDIR        (configuration in the environment)
#   AXG_LEAN             lean binary (required)
#   AXG_LEAN_PATH        roots for the module check: final module, statement copy, their imports (required)
#   AXG_SETUP            optional `lean --setup` JSON for the module check (importArts restricted to public .olean)
#   AXG_FROZEN_LEAN_PATH roots for the plain check: the build of the statement tree (S43.Statements) + Mathlib (required)
#   AXG_FINAL            final module (default S43KFinal);  AXG_STMT statement module name (default S43.Statements)
#   AXG_PAIRS            "K=N ..." (default S43K.Final.certificate=S43.Stmt.Cert.certificate
#                        S43K.Final.steiner_ratio_ge=S43.Stmt.Main.steiner_ratio_ge)
#   AXG_FROZEN           statement tree: a directory with S43/Statements.lean and a SHA256SUMS listing it (required)
#   AXG_STMT_SHA         sha256 of $AXG_FROZEN/S43/Statements.lean (default 1f96c6bfb4b408f36210e075e5d6925ad1c92d808b003a204feb80c4e3301cef)
#   AXG_STMT_COPY        source of the module-form copy (required): must equal form A or form B (see above) of the frozen
#                        S43/Statements.lean byte for byte
#   AXG_CONE_PREFIX      constant-name prefix of the compared cone (default S43)
#   AXG_TIMEOUT          seconds per lean run (default 3600)
# PASS iff (0) frozen sums + sha, copy text check; (1) each K is a theorem (an exported theorem shows as an axiom in a
# module env; a genuine axiom fails (2)) Expr-equal to N (copy) + rfl; (2) axioms of K
# (#print axioms and collectAxioms) within {propext, Classical.choice, Quot.sound}; (3) the S43* cone of each N has the same
# (type hash, value hash) lines in the module env (copy) and in the plain frozen env; (4) both lean runs rc 0, strict output.
# Writes OUTDIR/axgate_check_k.lean (module), axgate_check_f.lean (plain), their .out files, axgate_verdict.txt. Exit 0 iff PASS.
set -u
O=${1:?usage: axgate_v5.sh OUTDIR}
LEAN=${AXG_LEAN:?AXG_LEAN not set}; LP=${AXG_LEAN_PATH:?AXG_LEAN_PATH not set}; FLP=${AXG_FROZEN_LEAN_PATH:?AXG_FROZEN_LEAN_PATH not set}
COPY=${AXG_STMT_COPY:?AXG_STMT_COPY not set}
FINAL=${AXG_FINAL:-S43KFinal}; STMT=${AXG_STMT:-S43.Statements}; CP=${AXG_CONE_PREFIX:-S43}
PAIRS=${AXG_PAIRS:-"S43K.Final.certificate=S43.Stmt.Cert.certificate S43K.Final.steiner_ratio_ge=S43.Stmt.Main.steiner_ratio_ge"}
FROZEN=${AXG_FROZEN:?AXG_FROZEN not set}
SSHA=${AXG_STMT_SHA:-1f96c6bfb4b408f36210e075e5d6925ad1c92d808b003a204feb80c4e3301cef}
TMO=${AXG_TIMEOUT:-3600}
mkdir -p "$O" || exit 2
O=$(cd "$O" && pwd)   # absolute: the Lean runs write OUTDIR/cone_{k,f} from inside OUTDIR
V=$O/axgate_verdict.txt
verdict() { echo "$1" > "$V"; echo "$1"; case "$1" in PASS*) exit 0;; *) exit 1;; esac; }
# (0) frozen tree, statement sha, copy text
[ -f "$FROZEN/SHA256SUMS" ] || verdict "FAIL frozen: no SHA256SUMS in $FROZEN"
(cd "$FROZEN" && sha256sum -c --quiet SHA256SUMS) > "$O/frozen_check.txt" 2>&1 || verdict "FAIL frozen: sha256sum -c failed (see frozen_check.txt)"
n_line=$(awk -v s="$SSHA" '$1 == s && ($2 == "./S43/Statements.lean" || $2 == "S43/Statements.lean")' "$FROZEN/SHA256SUMS" | wc -l)
[ "$n_line" = 1 ] || verdict "FAIL frozen: SHA256SUMS has no S43/Statements.lean line with sha $SSHA"
TXT=$(python3 -I - "$COPY" "$FROZEN/S43/Statements.lean" <<'PYT'
import sys
copy, frozen = open(sys.argv[1], encoding='utf-8').read(), open(sys.argv[2], encoding='utf-8').read()
L = frozen.split('\n')
# form A: tools/to_module_v2.py (chain/n2m)
imp = [i for i, l in enumerate(L) if l.startswith('import ')]
last = imp[-1] if imp else -1
out = ['module', ''] + (['@[expose] public section', ''] if last < 0 else [])
for i, l in enumerate(L):
    out.append('public ' + l if l.startswith('import ') else l)
    if i == last:
        out += ['', '@[expose] public section']
form_a = '\n'.join(out).rstrip('\n') + '\n\nend\n'
# form B: the module header lines without A's blank lines (imports first)
i = 0
while i < len(L) and L[i].startswith('import '):
    i += 1
head = ['module'] + ['public ' + l for l in L[:i]] + ['@[expose] public section']
body = L[i:]
form_b = '\n'.join(head + body[:-1] + ['end', '']) if body and body[-1] == '' else '\n'.join(head + body + ['end'])
if copy == form_a:
    print('OK form A (to_module_v2)')
elif copy == form_b:
    print('OK form B (mkmodcopy_v1)')
else:
    c = copy.split('\n'); e = form_a.split('\n')
    for j in range(max(len(c), len(e))):
        if j >= len(c) or j >= len(e) or c[j] != e[j]:
            print('FAIL copy: matches neither module form of the frozen file; first difference to form A at line %d: %r vs %r'
                  % (j + 1, c[j][:60] if j < len(c) else None, e[j][:60] if j < len(e) else None)); break
PYT
)
case "$TXT" in OK*) ;; *) verdict "${TXT:-FAIL copy: text check produced no verdict}";; esac
META='
elab "#axgate_cone " n:ident : command => do
  let env ← getEnv
  let root := n.getId
  let pre := `CONEPREFIX
  let rec go (todo : List Name) (seen : NameSet) (fuel : Nat) : NameSet :=
    match fuel, todo with
    | 0, _ => seen
    | _, [] => seen
    | f + 1, c :: cs =>
      if seen.contains c then go cs seen f else
      match env.find? c with
      | none => go cs (seen.insert c) f
      | some ci =>
        let deps := ci.type.getUsedConstants.toList ++ (match ci with | .defnInfo d => d.value.getUsedConstants.toList | _ => [])
        go (deps.filter (fun d => pre.isPrefixOf d) ++ cs) (seen.insert c) f
  let start := match env.find? root with | some ci => ci.type.getUsedConstants.toList.filter (fun d => pre.isPrefixOf d) | none => []
  let cone := go start {} 1000000
  let etaE (e : Expr) : CommandElabM Expr :=
    liftTermElabM <| Meta.transform e (post := fun x => return .done x.eta)
  let dir := "CONEDIR"
  IO.FS.createDirAll dir
  for c in cone.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    match env.find? c with
    | some ci =>
      let te ← etaE ci.type
      IO.FS.writeFile (dir ++ "/" ++ c.toString ++ ".t") (toString te)
      match ci with
      | .defnInfo d =>
        let ve ← etaE d.value
        IO.FS.writeFile (dir ++ "/" ++ c.toString ++ ".v") (toString ve)
        logInfo m!"AXGATE-CONE {root} {c} {ci.type.hash} {d.value.hash} {te.hash} {ve.hash}"
      | _ => logInfo m!"AXGATE-CONE {root} {c} {ci.type.hash} - {te.hash} -"
    | none => logInfo m!"AXGATE-CONE {root} {c} missing - - -"
'
META=${META//CONEPREFIX/$CP}
CK=$O/axgate_check_k.lean; CF=$O/axgate_check_f.lean
{
  echo "module"; echo "public import Lean"; echo "import $FINAL"; echo "import $STMT"; echo ""
  echo "open Lean Elab Command in"
  echo "elab \"#axgate_pair \" k:ident n:ident : command => do"
  echo "  let env ← getEnv"
  echo "  let kn := k.getId"
  echo "  let nn := n.getId"
  echo "  -- a module importer sees exported theorems as axioms (their proofs stay private); a genuine axiom is caught by"
  echo "  -- the axiom check below (collectAxioms of an axiom lists the axiom itself)"
  echo "  let kc? := match env.find? kn with | some (.thmInfo t) => some t.toConstantVal | some (.axiomInfo t) => some t.toConstantVal | _ => none"
  echo "  match kc?, env.find? nn with"
  echo "  | some ck, some cn =>"
  echo "    if ck.type == cn.type && ck.levelParams == cn.levelParams then"
  echo "      logInfo m!\"AXGATE-EXPR-EQ {kn} {nn}\""
  echo "    else"
  echo "      logError m!\"AXGATE-EXPR-NE {kn} {nn}\""
  echo "    let ax ← Lean.collectAxioms kn"
  echo "    logInfo m!\"AXGATE-AXIOMS {kn} {ax.toList}\""
  echo "  | none, some _ => logError m!\"AXGATE-NOT-A-THEOREM {kn}\""
  echo "  | _, _ => logError m!\"AXGATE-MISSING {kn} {nn}\""
  echo ""; echo "open Lean Elab Command Meta in"; echo "${META//CONEDIR/$O/cone_k}"
  for p in $PAIRS; do k=${p%%=*}; n=${p#*=}
    echo "#axgate_pair $k $n"; echo "example : type_of% @$k = type_of% @$n := rfl"; echo "#print axioms $k"; echo "#axgate_cone $n"; echo ""
  done
} > "$CK"
{
  echo "import Lean"; echo "import $STMT"; echo ""; echo "open Lean Elab Command Meta in"; echo "${META//CONEDIR/$O/cone_f}"
  for p in $PAIRS; do n=${p#*=}; echo "#axgate_cone $n"; done
} > "$CF"
SETUPARG=""; [ -n "${AXG_SETUP:-}" ] && SETUPARG="--setup=$AXG_SETUP"
(cd "$O" && LEAN_PATH="$LP" LEAN_NUM_THREADS=1 timeout -k 10 "$TMO" "$LEAN" $SETUPARG -DElab.async=false -j1 axgate_check_k.lean) > "$O/axgate_check_k.out" 2>&1
rck=$?
(cd "$O" && LEAN_PATH="$FLP" LEAN_NUM_THREADS=1 timeout -k 10 "$TMO" "$LEAN" -DElab.async=false -j1 axgate_check_f.lean) > "$O/axgate_check_f.out" 2>&1
rcf=$?
R=$(python3 -I - "$O/axgate_check_k.out" "$rck" "$O/axgate_check_f.out" "$rcf" "$O" $PAIRS <<'PYG'
import re, sys
outk, rck, outf, rcf, odir = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
pairs = [p.split("=", 1) for p in sys.argv[6:]]
import hashlib, os
def dig(side, c, ext):
    p = os.path.join(odir, "cone_" + side, c + ext)
    return hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.exists(p) else None
STD = {"propext", "Classical.choice", "Quot.sound"}
pre = re.compile(r"^\S+:\d+:\d+: (info|warning|error): ")
def read(path):
    out = []
    for l in open(path, encoding="utf-8", errors="replace"):
        l = l.rstrip("\n")
        if not l.strip(): continue
        m = pre.match(l)
        out.append((m.group(1), l[m.end():]) if m else ("info", l))
    return out
probs, seen, conek, conef = [], {}, set(), set()
craw, ceta, etal = [0], [0], []
def bump(key): seen[key] = seen.get(key, 0) + 1
def axlist(s): s = s.strip(); return [] if s == "" else [a.strip() for a in s.split(",")]
for sev, body in read(outk):
    if sev != "info": probs.append("K " + sev + ": " + body[:150]); continue
    m1 = re.fullmatch(r"AXGATE-EXPR-EQ (\S+) (\S+)", body)
    m2 = re.fullmatch(r"AXGATE-AXIOMS (\S+) \[(.*)\]", body)
    m3 = re.fullmatch(r"'(\S+)' depends on axioms: \[(.*)\]", body)
    m4 = re.fullmatch(r"'(\S+)' does not depend on any axioms", body)
    m5 = re.fullmatch(r"AXGATE-CONE (\S+) (\S+) (\S+) (\S+) (\S+) (\S+)", body)
    if m1: bump(("eq", m1.group(1), m1.group(2)))
    elif m2:
        bump(("ax", m2.group(1))); bad = [x for x in axlist(m2.group(2)) if x not in STD]
        if bad: probs.append("collectAxioms of %s: %s" % (m2.group(1), ", ".join(bad)))
    elif m3:
        bump(("pr", m3.group(1))); bad = [x for x in axlist(m3.group(2)) if x not in STD]
        if bad: probs.append("#print axioms of %s: %s" % (m3.group(1), ", ".join(bad)))
    elif m4: bump(("pr", m4.group(1)))
    elif m5: conek.add(m5.groups())
    else: probs.append("K unexpected line: " + body[:150])
for sev, body in read(outf):
    m5 = re.fullmatch(r"AXGATE-CONE (\S+) (\S+) (\S+) (\S+) (\S+) (\S+)", body)
    if sev == "info" and m5: conef.add(m5.groups())
    else: probs.append("F " + sev + " " + body[:150])
for k, n in pairs:
    for key in (("eq", k, n), ("ax", k), ("pr", k)):
        if seen.get(key, 0) != 1: probs.append("expected one %s line for %s, got %d" % (key[0], k, seen.get(key, 0)))
    ck = {c[1]: c[2:] for c in conek if c[0] == n}; cf = {c[1]: c[2:] for c in conef if c[0] == n}
    if set(ck) != set(cf):
        probs.append("cone membership of %s differs: only module %s, only frozen %s" % (n, sorted(set(ck) - set(cf))[:3], sorted(set(cf) - set(ck))[:3]))
    for c in sorted(set(ck) & set(cf)):
        strong = all(dig("k", c, e) == dig("f", c, e) for e in (".t", ".v")) and dig("k", c, ".t") is not None
        if not strong or 'missing' in ck[c] or 'missing' in cf[c]:
            probs.append("cone of %s: %s differs (module %s, frozen %s; eta sha256 %s)" % (n, c, " ".join(ck[c]), " ".join(cf[c]),
                         "equal" if strong else "differ"))
        elif ck[c][:2] == cf[c][:2]: craw[0] += 1
        else: ceta[0] += 1; etal.append(c)
if not conef: probs.append("the frozen run printed no cone line at all")
if rck != 0: probs.insert(0, "module check rc %d" % rck)
if rcf != 0: probs.insert(0, "frozen check rc %d" % rcf)
ncone = sum(len({c for c in conef if c[0] == n}) for _, n in pairs)
open(sys.argv[1].rsplit('/', 1)[0] + '/axgate_problems.txt', 'w').write(''.join(p + '\n' for p in probs) +
    ''.join('eta-equal (not a problem): %s\n' % c for c in etal))
cats = {}
for p in probs:
    key = ('axioms' if 'xioms of' in p else 'cone' if p.startswith('cone') else 'expr' if 'EXPR' in p or 'expected one' in p
           else 'rc' if ' rc ' in p else 'K-error' if p.startswith('K error') else 'unexpected' if 'unexpected' in p else 'other')
    cats[key] = cats.get(key, 0) + 1
conetxt = "cone raw-equal %d, eta-equal %d%s, differ %d (sha256 of eta forms)" % (craw[0], ceta[0], (" [" + ", ".join(etal) + "]") if etal else "", sum(1 for p in probs if p.startswith("cone of")))
print(("PASS %d/%d pairs: Expr-equal + rfl, std-3 axioms, %s (of %d)" % (len(pairs), len(pairs), conetxt, ncone)) if not probs else
      "FAIL %d problems [%s]; %s; first: %s" % (len(probs), ", ".join("%s %d" % kv for kv in sorted(cats.items())), conetxt, " | ".join(probs[:3])))
PYG
)
[ -n "$R" ] || R="FAIL gate parser produced no verdict"
case "$R" in PASS*) verdict "$R; copy = frozen $(basename "$FROZEN") in module ${TXT#OK }; final $FINAL";; *) verdict "$R";; esac
