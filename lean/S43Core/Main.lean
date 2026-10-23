import S43Core.Check

/-! # s43check: run the Lean checker natively over a record file (timing tool)

usage: s43check FAMILY SUBCASE CERT.bin RHO_P RHO_Q START COUNT     (records in the ID64 layout of gen43f -DID64:
uint64 id, nb x (double lo, double hi), int32 split id, int32 lemma id; COUNT = 0: to the end)
Doubles are converted exactly to mantissas at scale 2^-P (a record with a non-dyadic-exact, NaN, -inf or infinite lower
value is reported as a failure). Prints one line with the counts and the elapsed time. -/

open S43

def u64At (b : ByteArray) (o : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc i => acc ||| ((b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64)) 0

def i32At (b : ByteArray) (o : Nat) : Int :=
  let v := (List.range 4).foldl (fun acc i => acc + (b.get! (o + i)).toNat * 256 ^ i) 0
  if v ≥ 2 ^ 31 then (v : Int) - 2 ^ 32 else v

/-- exact value of an IEEE double times 2^P: `some (some m)`, `some none` for +infinity, `none` if not representable -/
def decodeD (w : UInt64) : Option (Option Int) :=
  let sign := (w >>> 63).toNat
  let e := ((w >>> 52) &&& 0x7FF).toNat
  let fr := (w &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0x7FF then (if fr == 0 && sign == 0 then some none else none)
  else
    let M : Nat := if e == 0 then fr else fr + 2 ^ 52
    let ex : Int := (if e == 0 then (1 : Int) else (e : Int)) - 1075 + (P : Int)
    let mag : Option Nat :=
      if ex ≥ 0 then some (M <<< ex.toNat)
      else
        let k := (-ex).toNat
        if M % 2 ^ k == 0 then some (M >>> k) else none
    mag.map fun m => some (if sign == 1 then -(m : Int) else (m : Int))

def main (args : List String) : IO UInt32 := do
  match args with
  | [fam, sub, path, rp, rq, st, ct] =>
    let steiner := fam == "d_steiner"
    let fval := if sub == "f_ge_d" then 2 else if sub == "f_ge_dv" then 3 else 1
    let C := mkCase steiner fval
    let rho := DI.ofRat rp.toInt! rq.toNat!
    let data ← IO.FS.readBinFile path
    let rs := 8 + 16 * C.nb + 8
    let R := data.size / rs
    if data.size % rs != 0 then
      IO.println "{\"error\": \"size not a multiple of the record size\"}"; return 1
    let start := min st.toNat! R
    let cnt := if ct.toNat! == 0 || start + ct.toNat! > R then R - start else ct.toNat!
    let t0 ← IO.monoNanosNow
    let mut ok := 0; let mut ssym := 0; let mut ssub := 0; let mut fail := 0
    let mut fails : Array String := #[]
    for k in [start:start + cnt] do
      let o := k * rs
      let mut lo : Array Int := #[]; let mut hi : Array (Option Int) := #[]; let mut bad := false
      for i in [0:C.nb] do
        match decodeD (u64At data (o + 8 + 16 * i)), decodeD (u64At data (o + 16 + 16 * i)) with
        | some (some l), some h => lo := lo.push l; hi := hi.push h
        | _, _ => bad := true; lo := lo.push 0; hi := hi.push (some 0)
      let sid := i32At data (o + 8 + 16 * C.nb)
      let lid := i32At data (o + 12 + 16 * C.nb)
      let v := if bad then Verdict.fail else checkRecord C rho ⟨lo, hi⟩ sid lid
      match v with
      | .ok => ok := ok + 1
      | .skipSym => ssym := ssym + 1
      | .skipSub => ssub := ssub + 1
      | .fail =>
        fail := fail + 1
        if fails.size < 10 then fails := fails.push s!"\{\"rec\": {k}, \"split\": {sid}, \"lemma\": {lid}}"
    let t1 ← IO.monoNanosNow
    let secs := (t1 - t0).toFloat / 1e9
    IO.println s!"\{\"start\": {start}, \"count\": {cnt}, \"ok\": {ok}, \"skip_sym\": {ssym}, \"skip_sub\": {ssub}, \"fail\": {fail}, \"fails\": [{", ".intercalate fails.toList}], \"secs\": {secs}}"
    return (if fail == 0 then 0 else 1)
  | _ =>
    IO.println "usage: s43check FAMILY SUBCASE CERT.bin RHO_P RHO_Q START COUNT"; return 2
