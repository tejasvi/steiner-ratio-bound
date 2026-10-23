import S43Core.Splits
import S43Core.Vertex

/-! # The record check (port of the record loop of `indep43c.c`, version 3)

A record is a box (lower ends finite, upper ends finite or `none` = +infinity), a split id (1-based) and a lemma id. The
result is `.ok`, `.skipSym` / `.skipSub` (box entirely outside the WLOG region / outside the subcase) or `.fail`.
Written functionally for the soundness proof (`S43.Sound`); the verdicts are those of `indep43c.c` v3, plus a check that
the lower ends are `≥ 0` (always true for boxes of the tree). -/

namespace S43
open DI

inductive Verdict | ok | skipSym | skipSub | fail
  deriving DecidableEq, Repr, Inhabited

/-- a case: family ids, `fval` (1: f <= d, 2: f >= d with f := d, 3: f >= d with f a box variable), box dimension `nb` -/
structure Case where
  I : Ids
  fval : Nat
  nb : Nat
  splits : Array Split

def mkCase (steiner : Bool) (fval : Nat) : Case :=
  let I := if steiner then idsSt else idsReg
  ⟨I, fval, if fval == 2 then I.NV - 1 else I.NV, if steiner then splitsSt else splitsReg⟩

structure Box where
  lo : Array Int            -- mantissas at scale 2^-P
  hi : Array (Option Int)   -- none = +infinity
  deriving Inhabited

def bit (m i : Nat) : Bool := (m >>> i) % 2 == 1

/-- the variable values at a vertex: coordinate `j < nb` is `ch j`; with f := d (fval 2), `V[vf] = V[vd]` -/
def vertexV (C : Case) (ch : Nat → Int) : Array DI :=
  Array.ofFn (n := C.I.NV) fun j =>
    if j.val < C.nb then DI.ofMant (ch j.val)
    else if C.fval == 2 && j.val == C.I.vf then DI.ofMant (ch C.I.vd) else DI.zero

/-- `f ch` at every vertex of the finite face; coordinates `< k` are still to be chosen (lower end, or finite upper end) -/
def allVerts (f : (Nat → Int) → Bool) (bx : Box) : Nat → (Nat → Int) → Bool
  | 0, ch => f ch
  | k + 1, ch =>
    allVerts f bx k (fun j => if j == k then bx.lo[k]! else ch j) &&
    (match bx.hi[k]! with
     | some h => allVerts f bx k (fun j => if j == k then h else ch j)
     | none => true)

def hasY (I : Ids) (sp : Split) : Bool :=
  (List.zip sp.ta.toList sp.tb.toList).any fun e => e.1 == I.nY || e.2 == I.nY
def hasAX (I : Ids) (sp : Split) : Bool :=
  (List.zip sp.ta.toList sp.tb.toList).any fun e => (e.1 == I.nX && e.2 == I.nA) || (e.1 == I.nA && e.2 == I.nX)
/-- the extension rule of the subcase f >= d (f a box variable): Q in S+ implies the edge PQ in S- -/
def extOK (I : Ids) (sp : Split) : Bool := !(sp.sp.contains I.nQ) || sp.sm.contains (I.vf + 1)

/-- coordinate `i`: lower end `≥ 0`; finite with `lo ≤ hi`, or infinite and allowed to grow -/
def sideOK (C : Case) (sp : Split) (L : Nat) (bx : Box) (i : Nat) : Bool :=
  decide (0 ≤ bx.lo[i]!) &&
  match bx.hi[i]! with
  | some h => decide (bx.lo[i]! ≤ h)
  | none => if C.fval == 3 && i == C.I.vf then !hasY C.I sp && extOK C.I sp else bit sp.mono i && L == 0

def staticOK (C : Case) (sp : Split) (L : Nat) (bx : Box) : Bool :=
  (C.fval != 2 || bit sp.mono C.I.vf) &&
  (List.range C.nb).all (sideOK C sp L bx) &&
  !(C.fval == 3 && hasY C.I sp && (List.range C.nb).any (fun i => bx.hi[i]!.isNone)) &&
  -- v3: no A-X edge on a box with c unbounded
  !(hasAX C.I sp && bx.hi[C.I.vc]!.isNone)

/-- max(lo_u, lo_v) > max(hi_b, 1): the box lies outside max(u, v) <= max(b, 1) -/
def skipSym (I : Ids) (bx : Box) : Bool :=
  I.steiner && match bx.hi[I.vb]! with
    | some hb => decide (imax hb (1 <<< P) < imax bx.lo[I.vu]! bx.lo[I.vv]!)
    | none => false

/-- the box lies outside the subcase (f > d everywhere for fval 1, f < d everywhere for fval 3) -/
def skipSub (C : Case) (bx : Box) : Bool :=
  (C.fval == 1 && match bx.hi[C.I.vd]! with | some hd => decide (hd < bx.lo[C.I.vf]!) | none => false) ||
  (C.fval == 3 && match bx.hi[C.I.vf]! with | some hf => decide (hf < bx.lo[C.I.vd]!) | none => false)

/-- the record check at rho (an interval enclosing the exact rho) -/
def checkRecord (C : Case) (rho : DI) (bx : Box) (sid lid : Int) : Verdict :=
  if bx.lo.size != C.nb || bx.hi.size != C.nb then .fail
  else if skipSym C.I bx then .skipSym
  else if skipSub C bx then .skipSub
  else if sid < 1 || sid > C.splits.size || lid < 0 || lid > 8 then .fail
  else
    let sp := C.splits[sid.toNat - 1]!
    let L := lid.toNat
    if staticOK C sp L bx && allVerts (fun ch => evalVertexN C.I C.fval rho (vertexV C ch) sp L) bx C.nb (fun _ => 0)
    then .ok else .fail

end S43
