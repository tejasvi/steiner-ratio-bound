import S43Core.Tree
/-! s43tree FAMILY SUBCASE TREE.txt RHO_P RHO_Q MODE N : replay the compact stream (pilot / timing tool)
MODE `count`: verdict counts over the first N roots (N = 0: all); MODE `all`: `checkAll` (the function of the proof). -/
open S43

/-- root box `m` exactly as `walkTop` makes it -/
def rootOf (nb m : Nat) : Option Box :=
  (List.range nb).reverse.foldlM (fun bx k => (halves bx k).map fun (l, r) => if bit m k then r else l) (topBox nb)

structure Cnt where
  ok : Nat := 0
  sym : Nat := 0
  sub : Nat := 0
  fail : Nat := 0

partial def walkCount (C : Case) (rho : DI) (cs : Codes) (i : Nat) (bx : Box) (c : Cnt) : Option (Nat × Cnt) :=
  if i ≥ cs.size then none else
  let k := cs.get i
  if 33 ≤ k && k < 33 + C.nb then
    match halves bx (k - 33) with
    | none => none
    | some (l, r) => match walkCount C rho cs (i + 1) l c with
      | none => none
      | some (i1, c1) => walkCount C rho cs i1 r c1
  else match leafAt cs i with
    | none => none
    | some (lid, sid) =>
      let c' := match checkRecord C rho bx sid lid with
        | .ok => { c with ok := c.ok + 1 } | .skipSym => { c with sym := c.sym + 1 }
        | .skipSub => { c with sub := c.sub + 1 } | .fail => { c with fail := c.fail + 1 }
      some (i + 3, c')

def main (args : List String) : IO UInt32 := do
  match args with
  | [fam, sub, path, rp, rq, mode, n] =>
    let C := mkCase (fam == "d_steiner") (if sub == "f_ge_d" then 2 else if sub == "f_ge_dv" then 3 else 1)
    let rho := DI.ofRat rp.toInt! rq.toNat!
    let cs := Codes.ofBytes (← IO.FS.readBinFile path)
    let t0 ← IO.monoNanosNow
    if mode == "all" then
      let r := checkAll C rho cs
      let t1 ← IO.monoNanosNow
      IO.println s!"\{\"checkAll\": {r}, \"secs\": {(t1 - t0).toFloat / 1e9}}"
      return (if r then 0 else 1)
    let nr := if n.toNat! == 0 then 2 ^ C.nb else min n.toNat! (2 ^ C.nb)
    let mut i := 0; let mut c : Cnt := {}
    for m in [0:nr] do
      match rootOf C.nb m with
      | none => IO.println "{\"error\": \"root\"}"; return 1
      | some bx =>
        match walkCount C rho cs i bx c with
        | none => IO.println s!"\{\"error\": \"malformed stream in root {m}\"}"; return 1
        | some (i', c') => i := i'; c := c'
    let t1 ← IO.monoNanosNow
    IO.println s!"\{\"roots\": {nr}, \"pos\": {i}, \"ok\": {c.ok}, \"skip_sym\": {c.sym}, \"skip_sub\": {c.sub}, \"fail\": {c.fail}, \"secs\": {(t1 - t0).toFloat / 1e9}}"
    return 0
  | _ => IO.println "usage: s43tree FAMILY SUBCASE TREE.txt RHO_P RHO_Q MODE N"; return 2
