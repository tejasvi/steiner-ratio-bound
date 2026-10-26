module

public import S43Core.Interval

@[expose] public section

/-! # Geometry of the two local configurations and the value of a split at one vertex

A line-by-line port of the certificate checker `indep43c.c` (version 3): coordinates of the configuration
points, distances, the 3-point Steiner tree bound, the explicit 4-point network, the trapped-point lemma bounds and their
conditions (published lemmas 0-8, Lemma Y2, Lemma X2), and `evalVertex`, which decides whether
`rho L(T*) + L(S+) - L(S-) <= 0` certainly holds at the current vertex. Core Lean only. -/

namespace S43
open DI

/-- node and variable indices of a family (as in `indep43c.c`, `setup`) -/
structure Ids where
  steiner : Bool
  nA : Nat
  nB : Nat
  nD : Nat
  nU : Nat
  nV : Nat
  nP : Nat
  nQ : Nat
  nR : Nat
  nS : Nat
  nr : Nat
  nX : Nat
  nY : Nat
  vb : Nat
  vc : Nat
  vd : Nat
  vs : Nat
  vu : Nat
  vv : Nat
  ve : Nat
  vf : Nat
  NV : Nat
  nNodes : Nat

/-- d_steiner: nodes A B D U V P Q R s r X Y, variables b c d s u v e f -/
def idsSt : Ids := ⟨true, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 12⟩
/-- d_regular: nodes A B D P Q R s r X Y, variables b c d s e f (U, V and u, v unused) -/
def idsReg : Ids := ⟨false, 0, 1, 2, 99, 99, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 99, 99, 4, 5, 6, 10⟩

abbrev Pt := DI × DI

def dist (a b : Pt) : DI := ((a.1 - b.1).sq + (a.2 - b.2).sq).sqrt

/-- `src + t dir1` (`sgn = true`) or `src + t dir2`, `dir1 = (1/2, sqrt3/2)`, `dir2 = (1/2, -sqrt3/2)`; `neg` flips `t` -/
def addDir (src : Pt) (t : DI) (sgn : Bool) (negT : Bool) : Pt :=
  let h0 := t.half; let k0 := h0 * SQ3
  let h := if negT then h0.neg else h0
  let k := if negT then k0.neg else k0
  (src.1 + h, if sgn then src.2 + k else src.2 - k)

/-- the configuration points at the variable values `V` -/
def coords (I : Ids) (V : Array DI) : Array Pt := Id.run do
  let z : Pt := (DI.zero, DI.zero)
  let mut P : Array Pt := Array.replicate I.nNodes z
  let s : Pt := (DI.one, DI.zero)
  P := P.set! I.nA z
  P := P.set! I.nS s
  P := P.set! I.nB (addDir s V[I.vb]! true false)
  let r := addDir s V[I.vs]! false false
  P := P.set! I.nr r
  let Pp := addDir r V[I.vc]! true true
  P := P.set! I.nP Pp
  let D : Pt := (r.1 + V[I.vd]!, r.2)
  P := P.set! I.nD D
  if I.steiner then
    P := P.set! I.nU (addDir D V[I.vu]! true false)
    P := P.set! I.nV (addDir D V[I.vv]! false false)
  P := P.set! I.nQ (addDir Pp V[I.vf]! false false)
  P := P.set! I.nR (Pp.1 - V[I.ve]!, Pp.2)
  return P

def dabs (x : DI) : DI := if 0 ≤ x.lo then x else if x.hi ≤ 0 then x.neg else ⟨0, imax (-x.lo) x.hi⟩

/-- certainly angle(u, v) <= 120 degrees -/
def angleLe120Vec (ux uy vx vy : DI) : Bool :=
  let d := ux * vx + uy * vy
  if d.nonneg then true
  else (d.sq.nmul 4).lec ((ux.sq + uy.sq) * (vx.sq + vy.sq))

def angleLe120 (a b c : Pt) : Bool := angleLe120Vec (a.1 - b.1) (a.2 - b.2) (c.1 - b.1) (c.2 - b.2)

/-- upper bound of the 3-point Steiner minimal tree length (exact Fermat-Torricelli value when the angle tests decide) -/
def smt3 (a b c : Pt) : DI :=
  if !angleLe120 a b c then dist a b + dist b c
  else if !angleLe120 b c a then dist b c + dist c a
  else if !angleLe120 c a b then dist c a + dist a b
  else
    let ux := b.1 - a.1; let uy := b.2 - a.2; let vx := c.1 - a.1; let vy := c.2 - a.2
    let S := (dabs (ux * vy - uy * vx)).half
    let q := ((ux.sq + uy.sq) + (vx.sq + vy.sq) + ((b.1 - c.1).sq + (b.2 - c.2).sq)).half
    (q + (S * SQ3).nmul 2).sqrt

def maxdist (P : Array Pt) (w : Nat) (l : List Nat) : DI :=
  match l with
  | [] => DI.zero
  | x :: xs => xs.foldl (fun z y => z.max (dist P[w]! P[y]!)) (dist P[w]! P[x]!)

/-! ## The explicit 4-point network (NET4) -/

def toF (x : DI) : Float := (Float.ofInt (x.lo + x.hi)).scaleB (-((P : Int) + 1))
/-- the dyadic `round(x 2^40) / 2^40` as an exact interval (any point works: only the length evaluation is rigorous) -/
def ofF (x : Float) : DI :=
  let v := (x.scaleB 40).round
  let m : Int := if v < 0 then -((Float.toUInt64 (-v)).toNat : Int) else ((Float.toUInt64 v).toNat : Int)
  DI.ofMant (m <<< (P - 40))

def wzStep (Z O : Float × Float) (a b : Float × Float) : Float × Float :=
  let nb := [a, b, O]
  let (ws, sx, sy) := nb.foldl (fun (acc : Float × Float × Float) (q : Float × Float) =>
    let d0 := Float.sqrt ((Z.1 - q.1) * (Z.1 - q.1) + (Z.2 - q.2) * (Z.2 - q.2))
    let d := if d0 < 1e-15 then 1e-15 else d0
    (acc.1 + 1 / d, acc.2.1 + q.1 / d, acc.2.2 + q.2 / d)) (0, 0, 0)
  (sx / ws, sy / ws)

def wzIter : Nat → (Float × Float) → (Float × Float) → (Float × Float) → (Float × Float) → (Float × Float) →
    (Float × Float) → (Float × Float) × (Float × Float)
  | 0, x, y, _, _, _, _ => (x, y)
  | n + 1, x, y, p1, p2, p3, p4 =>
    let x' := wzStep x y p1 p2
    let y' := wzStep y x' p3 p4
    wzIter n x' y' p1 p2 p3 p4

/-- number of Weiszfeld alternations (the checker's NET4_ITV) -/
def NET4_ITV : Nat := 300

/-- length of the network p1-x, p2-x, x-y, p3-y, p4-y for numerically optimised x, y, evaluated in intervals -/
def net4 (p1 p2 p3 p4 : Pt) : DI :=
  let f := fun (p : Pt) => (toF p.1, toF p.2)
  let (q1, q2, q3, q4) := (f p1, f p2, f p3, f p4)
  let x0 := ((q1.1 + q2.1) / 2, (q1.2 + q2.2) / 2)
  let y0 := ((q3.1 + q4.1) / 2, (q3.2 + q4.2) / 2)
  let (x, y) := wzIter NET4_ITV x0 y0 q1 q2 q3 q4
  let X : Pt := (ofF x.1, ofF x.2); let Y : Pt := (ofF y.1, ofF y.2)
  dist p1 X + dist p2 X + dist X Y + dist p3 Y + dist p4 Y

/-! ## Lemma conditions and bounds -/

inductive Key | AX | UX | VX | DX | Y | ADQR | BDQR
  deriving DecidableEq

/-- Lemma Y2 (d_regular, f a box variable): Psi > 0 certainly (smt3 is an upper bound, so the computed Psi is a lower bound) -/
def psiY2Pos (I : Ids) (V : Array DI) (P : Array Pt) : Bool :=
  let b := V[I.vb]!; let c := V[I.vc]!; let d := V[I.vd]!; let s := V[I.vs]!; let e := V[I.ve]!; let f := V[I.vf]!
  let psi0 := DI.one + b + s + d.nmul 3 + c.nmul 2 + e
  let Q := P[I.nQ]!
  let Qs : Pt := (Q.1 + (d.nmul 2 + c - f), Q.2)
  let psi := psi0 - smt3 P[I.nA]! P[I.nB]! P[I.nD]! - smt3 P[I.nD]! Q Qs - dist Q P[I.nR]!
  psi.pos

/-- lemma 5's condition `e < kc` (`kc = (2/sqrt3 - 1) c`), extended by Lemma X2: `e < c` and `Phi_X > 0` certainly -/
def x2Cond (I : Ids) (V : Array DI) (kc : DI) : Bool :=
  let c := V[I.vc]!; let e := V[I.ve]!; let f := V[I.vf]!
  if e.ltc kc then true
  else if !(e.ltc c) then false
  else
    let t := (e.sq + e * f + f.sq).sqrt
    let phi := c + e + f - t - ((c + e) * SQ3).half
    phi.pos

/-- lemma entry for (lemma L, key K): `none` = no such entry; `some none` = condition fails; `some (some z)` = bound z -/
def lemmaEntry (I : Ids) (fval : Nat) (V : Array DI) (P : Array Pt) (L : Nat) (K : Key) : Option (Option DI) :=
  let b := V[I.vb]!; let c := V[I.vc]!; let d := V[I.vd]!; let s := V[I.vs]!; let e := V[I.ve]!
  match K with
  | .Y =>
    if fval == 3 && !I.steiner then
      if !psiY2Pos I V P then some none else some (some (maxdist P I.nD [I.nP, I.nQ]))
    else if fval != 1 then some none
    else if I.steiner then some (some (maxdist P I.nV [I.nr, I.nP, I.nQ]))
    else some (some (maxdist P I.nD [I.nP, I.nQ]))
  | .AX =>
    match L with
    | 0 => if !(c.lec DI.one) then some none else some (some (maxdist P I.nA [I.nr, I.nP]))
    | 1 | 2 =>
      let a := if L == 1 then (((s.div SQ3).getD ⟨0, 0⟩).nmul 2 - c + DI.one) else (TWO_OVER_SQ3_M1 * c + DI.one)
      let bb := c + e
      if !(e.ltc a && bb.gec DI.one) then some none
      else
        let z := maxdist P I.nA [I.nS, I.nr, I.nP, I.nR]
        some (some (z.max (((bb - DI.one) * SQ3).half)))
    | 5 => if !x2Cond I V (TWO_OVER_SQ3_M1 * c) then some none else some (some (maxdist P I.nA [I.nr, I.nP, I.nR]))
    | 8 =>
      if !(e.ltc (s + DI.one)) then some none
      else some (some ((maxdist P I.nA [I.nr, I.nP, I.nR]).max (e + c - DI.one)))
    | _ => none
  | .UX | .VX | .DX =>
    if L != 5 then none
    else if (K == .DX) == I.steiner then none
    else if !x2Cond I V (TWO_OVER_SQ3_M1 * c) then some none
    else
      let W := if K == .UX then I.nU else if K == .VX then I.nV else I.nD
      let R := P[I.nR]!
      let h := (c - e).half.half
      let H : Pt := (R.1 - h, R.2 + h * SQ3)
      some (some ((maxdist P W [I.nr, I.nP, I.nR]).max (dist P[W]! H)))
  | .ADQR =>
    if L == 3 then
      let ok1 := (c + e).gec DI.one && e.lec (s + c + d + DI.ofInt 2) && e.gec (DI.ofInt 2 - c - d + s)
      let lhs := (DI.ofInt 2 + c + d.nmul 3 + s) * e
      let rhs := DI.ofInt 2 + c.sq + d.nmul 3 + s.nmul 2 + (c * s).nmul 3 + (d * s).nmul 3 + s.sq.nmul 2
      let ok2 := lhs.lec rhs && e.lec (s.nmul 3)
      if !(ok1 && ok2) then some none
      else
        let D := P[I.nD]!; let R := P[I.nR]!; let Q := P[I.nQ]!; let A := P[I.nA]!
        let okang0 := angleLe120Vec (D.1 - R.1) (D.2 - R.2) (Q.1 - A.1) (Q.2 - A.2)
        let ux := Q.1 - D.1; let uy := Q.2 - D.2
        let vx := ux.half - (uy * SQ3).half; let vy := (ux * SQ3).half + uy.half
        let Vp : Pt := (D.1 + vx, D.2 + vy)
        if !(okang0 && angleLe120 A R Vp && angleLe120 R A Vp) then some none
        else
          let X := (DI.one + e + d.nmul 3 + s.nmul 2 + c.nmul 3).half
          let Y := ((c + d + e - DI.one) * SQ3).half
          some (some (X.sq + Y.sq).sqrt)
    else if L == 4 then
      if !(c.gec DI.one && e.gec DI.one) then some none
      else
        let S := DI.one + s + c + e + d.nmul 2
        some (some (S.sq - S + DI.one).sqrt)
    else if L == 7 then
      let a1 := d * (c + e - DI.one) + e * (s + c)
      let k := c + s + d.nmul 2
      let b1 := ((k.sq + d.nmul 4).sqrt - k).half
      let a2 := (c * (s + c + d)).nmul 3 - (DI.ofInt 2 + s - c + d) * (c + e.nmul 2 + d.nmul 2)
      let ok := a1.nonneg && e.gec b1 && a2.nonneg && (s + e).gec DI.one && c.lec ((s + e).half + d + DI.one)
      if !ok then some none
      else
        let S := d.nmul 2 + s + c + e
        some (some (S.sq + S + DI.one).sqrt)
    else none
  | .BDQR =>
    if L != 6 then none
    else if !(d.gec b) then some none
    else
      let t2 := c + d.nmul 2 + e + s
      let t1 := t2 + b.nmul 2
      some (some ((t1.sq + t2.sq.nmul 3).sqrt.half))

/-! ## One vertex -/

structure Split where
  sm : Array Nat
  sp : Array Nat
  ta : Array Nat
  tb : Array Nat
  mono : Nat
  deriving Inhabited

/-- T* edge touching X or Y -> key kind -/
def edgeKey (I : Ids) (a b : Nat) : Option Key :=
  let o := if a == I.nX || a == I.nY then b else a
  let imp := if a == I.nX || a == I.nY then a else b
  if imp == I.nX then
    if o == I.nA then some .AX
    else if I.steiner && o == I.nU then some .UX
    else if I.steiner && o == I.nV then some .VX
    else if !I.steiner && o == I.nD then some .DX
    else none
  else if imp == I.nY then
    if o == (if I.steiner then I.nV else I.nD) then some .Y else none
  else none

def sorted4 (l : List Nat) : List Nat := l.mergeSort (· ≤ ·)

/-- `true` = rho L(T*) + L(S+) - L(S-) <= 0 certainly at the variable values V (all lemma conditions certainly hold) -/
def evalVertex (I : Ids) (fval : Nat) (rho : DI) (V : Array DI) (sp : Split) (L : Nat) : Bool := Id.run do
  let P := coords I V
  -- T*
  let mut t := DI.zero
  for i in [0:sp.ta.size] do
    let a := sp.ta[i]!; let b := sp.tb[i]!
    if a == I.nX || b == I.nX || a == I.nY || b == I.nY then
      match edgeKey I a b with
      | none => return false
      | some K =>
        match lemmaEntry I fval V P L K with
        | some (some z) => t := t + z
        | _ => return false
    else t := t + dist P[a]! P[b]!
  -- S-
  let mut sm := DI.zero
  for e in sp.sm do
    sm := sm + (if e == 0 then DI.one else V[e - 1]!)
  -- S+
  let n := sp.sp.size
  let spl : DI ←
    if n ≤ 1 then pure DI.zero
    else if n == 2 then pure (dist P[sp.sp[0]!]! P[sp.sp[1]!]!)
    else if n == 3 then pure (smt3 P[sp.sp[0]!]! P[sp.sp[1]!]! P[sp.sp[2]!]!)
    else
      let s1 := sorted4 [I.nA, I.nD, I.nQ, I.nR]; let s2 := sorted4 [I.nB, I.nD, I.nQ, I.nR]
      let spl4 := sp.sp.toList
      if n == 4 && spl4 == s1 then
        if L == 3 then pure (net4 P[I.nA]! P[I.nR]! P[I.nD]! P[I.nQ]!)
        else if L == 4 || L == 7 then pure (net4 P[I.nA]! P[I.nD]! P[I.nQ]! P[I.nR]!)
        else return false
      else if n == 4 && spl4 == s2 then
        if L == 6 then pure (net4 P[I.nB]! P[I.nD]! P[I.nQ]! P[I.nR]!)
        else return false
      else return false
  let v := rho * t + spl - sm
  return v.nonpos

end S43

end
