module

public import S43CoreK.VertexK
public import S43CoreK.SplitsK

@[expose] public section

/-! # The record check of the kernel checker

Mirror of lean/'s `checkRecord` (`S43Core.Check`) in kernel-native data: box mantissas as `Nat`s (lower ends are `>= 0` in lean/'s
`sideOK`; upper ends `none` = +infinity), split id and lemma id as `Nat`s. Same verdicts: size check, `skipSym`,
`skipSub`, id range, `staticOK`, then the vertex test at every vertex of the finite face. -/

namespace S43K
open DN

inductive VerdictK | ok | skipSym | skipSub | fail
  deriving DecidableEq, Repr

structure BoxK where
  lo : List Nat
  hi : List (Option Nat)

def lget (l : List Nat) (i : Nat) : Nat := l.getD i 0
def hget (l : List (Option Nat)) (i : Nat) : Option Nat := l.getD i none
def bitK (m i : Nat) : Bool := Nat.beq (Nat.mod (Nat.shiftRight m i) 2) 1

/-- family indices: vb vc vd vs vu vv ve vf, nA nD nQ nX nY -/
def vfK (st : Bool) : Nat := bif st then 7 else 5
def nQK (st : Bool) : Nat := bif st then 6 else 4

def hasYK (st : Bool) : List Nat → List Nat → Bool
  | a :: as, b :: bs => Nat.beq a (nYK st) || Nat.beq b (nYK st) || hasYK st as bs
  | _, _ => false
def hasAXK (st : Bool) : List Nat → List Nat → Bool
  | a :: as, b :: bs => (Nat.beq a (nXK st) && Nat.beq b 0) || (Nat.beq a 0 && Nat.beq b (nXK st)) || hasAXK st as bs
  | _, _ => false
def memK (x : Nat) : List Nat → Bool
  | [] => false
  | a :: as => Nat.beq a x || memK x as
/-- the extension rule of f >= d (f a box variable): Q in S+ implies the edge PQ in S- -/
def extOKK (st : Bool) (sp : SplitK) : Bool := !(memK (nQK st) sp.sp) || memK (Nat.add (vfK st) 1) sp.sm

/-- lean/'s `sideOK` (the lower end is a `Nat`, so `0 <= lo` holds) -/
def sideOKK (st : Bool) (fval : Nat) (sp : SplitK) (L : Nat) (bx : BoxK) (i : Nat) : Bool :=
  match hget bx.hi i with
  | some h => Nat.ble (lget bx.lo i) h
  | none => bif Nat.beq fval 3 && Nat.beq i (vfK st) then !(hasYK st sp.ta sp.tb) && extOKK st sp
            else bitK sp.mono i && Nat.beq L 0

def allSides (st : Bool) (fval : Nat) (sp : SplitK) (L : Nat) (bx : BoxK) : Nat → Bool
  | 0 => true
  | k + 1 => sideOKK st fval sp L bx k && allSides st fval sp L bx k
def anyInf : List (Option Nat) → Bool
  | [] => false
  | none :: _ => true
  | some _ :: hs => anyInf hs

/-- lean/'s `staticOK` -/
def staticOKK (st : Bool) (fval nb : Nat) (sp : SplitK) (L : Nat) (bx : BoxK) : Bool :=
  (!(Nat.beq fval 2) || bitK sp.mono (vfK st)) && allSides st fval sp L bx nb &&
  !(Nat.beq fval 3 && hasYK st sp.ta sp.tb && anyInf bx.hi) &&
  !(hasAXK st sp.ta sp.tb && (hget bx.hi 1).isNone)

/-- lean/'s `skipSym`: d_steiner, `max(hi_b, 1) < max(lo_u, lo_v)` -/
def skipSymK (st : Bool) (bx : BoxK) : Bool :=
  st && match hget bx.hi 0 with
    | some hb => Nat.blt (nmax hb 1267650600228229401496703205376) (nmax (lget bx.lo 4) (lget bx.lo 5))
    | none => false
/-- lean/'s `skipSub` -/
def skipSubK (st : Bool) (fval : Nat) (bx : BoxK) : Bool :=
  (Nat.beq fval 1 && match hget bx.hi 2 with | some hd => Nat.blt hd (lget bx.lo (vfK st)) | none => false) ||
  (Nat.beq fval 3 && match hget bx.hi (vfK st) with | some hf => Nat.blt hf (lget bx.lo 2) | none => false)

/-- a box end as an exact interval, written with a salt `s` that does not change its value: Lean's `Hashable Nat` hashes
the low 64 bits only, and box ends at scale 2^-100 have >= 64 trailing zero bits, so without the salt every input
literal hashes alike and the kernel's whnf cache degenerates (quadratic time in the number of vertices of a record) -/
def ofMantS (m s : Nat) : DN := ⟨Nat.sub (Nat.add (Nat.add B m) s) s, Nat.sub (Nat.add (Nat.add B m) s) s⟩

/-- the vertex values from the chosen box values, last coordinate first (lean/'s `vertexV`; f := d when fval = 2) -/
def mkVars (st : Bool) : List DN → VarsK
  | [f, e, v, u, s, d, c, b] => ⟨b, c, d, s, u, v, e, f⟩
  | [e, v, u, s, d, c, b] => ⟨b, c, d, s, u, v, e, d⟩
  | [f, e, s, d, c, b] =>
    bif st then ⟨DN.zero, DN.zero, DN.zero, DN.zero, DN.zero, DN.zero, DN.zero, DN.zero⟩
    else ⟨b, c, d, s, DN.zero, DN.zero, e, f⟩
  | _ => ⟨DN.zero, DN.zero, DN.zero, DN.zero, DN.zero, DN.zero, DN.zero, DN.zero⟩

/-- `ev` at every vertex of the finite face (coordinate 0 outermost; the value is order-independent); coordinate `j`'s
lower end carries salt `2j+1`, its upper end `2j+2` -/
def allVK (ev : List DN → Bool) : Nat → List Nat → List (Option Nat) → List DN → Bool
  | j, l :: ls, h :: hs, acc =>
    allVK ev (Nat.add j 1) ls hs (ofMantS l (Nat.add (Nat.mul 2 j) 1) :: acc) &&
      (match h with | some hv => allVK ev (Nat.add j 1) ls hs (ofMantS hv (Nat.add (Nat.mul 2 j) 2) :: acc) | none => true)
  | _, _, _, acc => ev acc

def splitK (st : Bool) (sid : Nat) : SplitK := bif st then splitSt sid else splitReg sid
def nSplits (st : Bool) : Nat := bif st then 1418 else 158

def checkVerts (st : Bool) (fval L : Nat) (sp : SplitK) (bx : BoxK) : Bool :=
  allVK (fun acc => evalVertexK st fval L (mkVars st acc) sp) 0 bx.lo bx.hi []
/-- the static range bound: every box end (lower ends, finite upper ends) is below `2^126` (real 2^26), so
no `Nat.sub` in the evaluator can truncate (with witness points clamped to `|v| <= 2^120`) -/
def MB : Nat := 85070591730234615865843651857942052864
def allBelow : List Nat → Bool
  | [] => true
  | x :: xs => Nat.blt x MB && allBelow xs
def allBelowO : List (Option Nat) → Bool
  | [] => true
  | none :: hs => allBelowO hs
  | some h :: hs => Nat.blt h MB && allBelowO hs
def checkSp (st : Bool) (fval nb L : Nat) (sp : SplitK) (bx : BoxK) : VerdictK :=
  bif allBelow bx.lo && allBelowO bx.hi && staticOKK st fval nb sp L bx && checkVerts st fval L sp bx then .ok else .fail

/-- lean/'s `checkRecord` (rho = 2141/2500 built in) -/
def checkRecordK (st : Bool) (fval nb : Nat) (bx : BoxK) (sid lid : Nat) : VerdictK :=
  bif !(Nat.beq bx.lo.length nb) || !(Nat.beq bx.hi.length nb) then .fail
  else bif skipSymK st bx then .skipSym
  else bif skipSubK st fval bx then .skipSub
  else bif Nat.beq sid 0 || Nat.blt (nSplits st) sid || Nat.blt 8 lid then .fail
  else checkSp st fval nb lid (splitK st sid) bx

/-! ## Record-indexed salts (for many records inside ONE declaration: salts must differ across records too) -/
def allVKS (ev : List DN → Bool) (base : Nat) : Nat → List Nat → List (Option Nat) → List DN → Bool
  | j, l :: ls, h :: hs, acc =>
    allVKS ev base (Nat.add j 1) ls hs (ofMantS l (Nat.add base (Nat.add (Nat.mul 2 j) 1)) :: acc) &&
      (match h with
       | some hv => allVKS ev base (Nat.add j 1) ls hs (ofMantS hv (Nat.add base (Nat.add (Nat.mul 2 j) 2)) :: acc)
       | none => true)
  | _, _, _, acc => ev acc
def checkSpS (base : Nat) (st : Bool) (fval nb L : Nat) (sp : SplitK) (bx : BoxK) : VerdictK :=
  bif allBelow bx.lo && allBelowO bx.hi && staticOKK st fval nb sp L bx &&
      allVKS (fun acc => evalVertexK st fval L (mkVars st acc) sp) base 0 bx.lo bx.hi [] then .ok else .fail
/-- `checkRecordK` with salts offset by `base` (same verdict; only the input terms' hashes differ) -/
def checkRecordKS (base : Nat) (st : Bool) (fval nb : Nat) (bx : BoxK) (sid lid : Nat) : VerdictK :=
  bif !(Nat.beq bx.lo.length nb) || !(Nat.beq bx.hi.length nb) then .fail
  else bif skipSymK st bx then .skipSym
  else bif skipSubK st fval bx then .skipSub
  else bif Nat.beq sid 0 || Nat.blt (nSplits st) sid || Nat.blt 8 lid then .fail
  else checkSpS base st fval nb lid (splitK st sid) bx

end S43K

end
