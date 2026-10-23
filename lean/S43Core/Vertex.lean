import S43Core.Geom

/-! # The vertex evaluation of the Lean checker

Same values as the certificate checker `indep43c.c` (version 3), written so that every bound is visibly the length of an explicit
network: the 3-point bound is a two-edge path (a star centred at a terminal) or a star at a numerically computed Fermat
point, and the 4-point S+ bound is the network of `net4` at its numerically computed Steiner points. The Float code only
chooses the points (rounded to exact dyadics); every length is evaluated in outward-rounded intervals. The
`S43Core.Geom` of the statements is unchanged; this module replaces its `coords`, `smt3`, `psiY2Pos` and `evalVertex` in
the checker, and adds range checks on node ids (no-ops on the published splits). Core Lean only. -/

namespace S43
open DI

/-- the configuration points (as `S43.Stmt.Pts`; U and V only for d_steiner) -/
structure PtsDI where
  A : Pt
  B : Pt
  D : Pt
  U : Pt
  V : Pt
  P : Pt
  Q : Pt
  R : Pt
  s : Pt
  r : Pt

/-- the configuration points at the variable values `V` (the points of `coords`) -/
def ptsDI (I : Ids) (V : Array DI) : PtsDI :=
  let z : Pt := (DI.zero, DI.zero)
  let s : Pt := (DI.one, DI.zero)
  let r := addDir s V[I.vs]! false false
  let Pp := addDir r V[I.vc]! true true
  let D : Pt := (r.1 + V[I.vd]!, r.2)
  { A := z, B := addDir s V[I.vb]! true false, D := D,
    U := if I.steiner then addDir D V[I.vu]! true false else z,
    V := if I.steiner then addDir D V[I.vv]! false false else z,
    P := Pp, Q := addDir Pp V[I.vf]! false false, R := (Pp.1 - V[I.ve]!, Pp.2), s := s, r := r }

/-- the points by node id (X, Y unpositioned) -/
def coordsN (I : Ids) (V : Array DI) : Array Pt :=
  let p := ptsDI I V
  let z : Pt := (DI.zero, DI.zero)
  if I.steiner then #[p.A, p.B, p.D, p.U, p.V, p.P, p.Q, p.R, p.s, p.r, z, z]
  else #[p.A, p.B, p.D, p.P, p.Q, p.R, p.s, p.r, z, z]

/-! ## Explicit networks -/

/-- one Weiszfeld step for the point Z with the three neighbours a, b, c (unrolled, Float) -/
@[inline] def wz3 (Z a b c : Float × Float) : Float × Float :=
  let w := fun (q : Float × Float) =>
    let d0 := Float.sqrt ((Z.1 - q.1) * (Z.1 - q.1) + (Z.2 - q.2) * (Z.2 - q.2))
    1 / (if d0 < 1e-15 then 1e-15 else d0)
  let wa := w a; let wb := w b; let wc := w c
  let ws := wa + wb + wc
  ((wa * a.1 + wb * b.1 + wc * c.1) / ws, (wa * a.2 + wb * b.2 + wc * c.2) / ws)

/-- apex of the equilateral triangle on p q on the side opposite to r (Float) -/
def apex (p q r : Float × Float) : Float × Float :=
  let s3 := Float.sqrt 3 / 2
  let ux := q.1 - p.1; let uy := q.2 - p.2
  let e1 := (p.1 + ux / 2 - s3 * uy, p.2 + uy / 2 + s3 * ux)
  let e2 := (p.1 + ux / 2 + s3 * uy, p.2 + uy / 2 - s3 * ux)
  let side := fun (e : Float × Float) => ux * (e.2 - p.2) - uy * (e.1 - p.1)
  let sr := ux * (r.2 - p.2) - uy * (r.1 - p.1)
  if side e1 * sr < 0 then e1 else e2

/-- Fermat point by the Torricelli construction (intersection of a-E_a and b-E_b), polished by 3 Weiszfeld steps -/
def fermatPt (a b c : Float × Float) : Float × Float :=
  let ea := apex b c a; let eb := apex c a b
  let d1 := (ea.1 - a.1, ea.2 - a.2); let d2 := (eb.1 - b.1, eb.2 - b.2)
  let den := d1.1 * d2.2 - d1.2 * d2.1
  let x0 := if den.abs < 1e-300 then ((a.1 + b.1 + c.1) / 3, (a.2 + b.2 + c.2) / 3)
    else let t := ((b.1 - a.1) * d2.2 - (b.2 - a.2) * d2.1) / den; (a.1 + t * d1.1, a.2 + t * d1.2)
  wz3 (wz3 (wz3 x0 a b c) a b c) a b c

/-- the Steiner point of the 3-point star (an exact dyadic point) -/
def fermatW (a b c : Pt) : Pt :=
  let f := fun (p : Pt) => (toF p.1, toF p.2)
  let x := fermatPt (f a) (f b) (f c)
  (ofF x.1, ofF x.2)

/-- length of the star a-X, b-X, c-X -/
def star3 (a b c X : Pt) : DI := dist a X + dist b X + dist c X

/-- upper bound of the 3-point Steiner tree length: the two-edge path at a vertex whose angle is not certainly
<= 120 degrees, else the star at the computed Fermat point -/
def smt3n (a b c : Pt) : DI :=
  if !angleLe120 a b c then dist a b + dist b c
  else if !angleLe120 b c a then dist b c + dist c a
  else if !angleLe120 c a b then dist c a + dist a b
  else star3 a b c (fermatW a b c)

/-- the two Steiner points of the 4-point network p1-x, p2-x, x-y, p3-y, p4-y (Weiszfeld alternations, as `net4`) -/
def net4W (p1 p2 p3 p4 : Pt) : Pt × Pt :=
  let f := fun (p : Pt) => (toF p.1, toF p.2)
  let q1 := f p1; let q2 := f p2; let q3 := f p3; let q4 := f p4
  let x0 := ((q1.1 + q2.1) / 2, (q1.2 + q2.2) / 2)
  let y0 := ((q3.1 + q4.1) / 2, (q3.2 + q4.2) / 2)
  let r := wzIter NET4_ITV x0 y0 q1 q2 q3 q4
  ((ofF r.1.1, ofF r.1.2), (ofF r.2.1, ofF r.2.2))

/-- length of the network p1-X, p2-X, X-Y, p3-Y, p4-Y -/
def pair4 (p1 p2 p3 p4 : Pt) (XY : Pt × Pt) : DI :=
  dist p1 XY.1 + dist p2 XY.1 + dist XY.1 XY.2 + dist p3 XY.2 + dist p4 XY.2

def net4n (p1 p2 p3 p4 : Pt) : DI := pair4 p1 p2 p3 p4 (net4W p1 p2 p3 p4)

/-! ## Lemma Y2 and the lemma entries -/

/-- Lemma Y2 (d_regular, f a box variable): Psi > 0 certainly, with both SMT terms replaced by explicit networks -/
def psiY2PosN (I : Ids) (V : Array DI) (P : Array Pt) : Bool :=
  let b := V[I.vb]!; let c := V[I.vc]!; let d := V[I.vd]!; let s := V[I.vs]!; let e := V[I.ve]!; let f := V[I.vf]!
  let psi0 := DI.one + b + s + d.nmul 3 + c.nmul 2 + e
  let Q := P[I.nQ]!
  let Qs : Pt := (Q.1 + (d.nmul 2 + c - f), Q.2)
  let psi := psi0 - smt3n P[I.nA]! P[I.nB]! P[I.nD]! - smt3n P[I.nD]! Q Qs - dist Q P[I.nR]!
  psi.pos

/-- lemma entry: as `lemmaEntry`, with `psiY2PosN` for the Y bound of Lemma Y2 -/
def lemmaEntryN (I : Ids) (fval : Nat) (V : Array DI) (P : Array Pt) (L : Nat) (K : Key) : Option (Option DI) :=
  match K with
  | .Y =>
    if fval == 3 && !I.steiner then
      if !psiY2PosN I V P then some none else some (some (maxdist P I.nD [I.nP, I.nQ]))
    else if fval != 1 then some none
    else if I.steiner then some (some (maxdist P I.nV [I.nr, I.nP, I.nQ]))
    else some (some (maxdist P I.nD [I.nP, I.nQ]))
  | K => lemmaEntry I fval V P L K

/-! ## One vertex -/

/-- value of one T* edge: a distance between positioned nodes, or the bound of the lemma entry for a trapped-point edge
(`none` = not certified) -/
def edgeValN (I : Ids) (fval : Nat) (V : Array DI) (P : Array Pt) (L : Nat) (a b : Nat) : Option DI :=
  if a == I.nX || b == I.nX || a == I.nY || b == I.nY then
    match edgeKey I a b with
    | none => none
    | some K => match lemmaEntryN I fval V P L K with
      | some (some z) => some z
      | _ => none
  else if a < I.nX && b < I.nX then some (dist P[a]! P[b]!) else none

/-- the S+ value: 0, a distance, the 3-point bound, or the 4-point network with the pairing of lemma L -/
def spDIN (I : Ids) (P : Array Pt) (sp : Split) (L : Nat) : Option DI :=
  if !(sp.sp.toList.all (· < I.nX)) then none else
  match sp.sp.toList with
  | [] => some DI.zero
  | [_] => some DI.zero
  | [a, b] => some (dist P[a]! P[b]!)
  | [a, b, c] => some (smt3n P[a]! P[b]! P[c]!)
  | [a, b, c, d] =>
    if [a, b, c, d] == sorted4 [I.nA, I.nD, I.nQ, I.nR] then
      if L == 3 then some (net4n P[I.nA]! P[I.nR]! P[I.nD]! P[I.nQ]!)
      else if L == 4 || L == 7 then some (net4n P[I.nA]! P[I.nD]! P[I.nQ]! P[I.nR]!)
      else none
    else if [a, b, c, d] == sorted4 [I.nB, I.nD, I.nQ, I.nR] then
      if L == 6 then some (net4n P[I.nB]! P[I.nD]! P[I.nQ]! P[I.nR]!) else none
    else none
  | _ => none

/-- the S- length -/
def smDIN (V : Array DI) (sp : Split) : DI :=
  sp.sm.toList.foldl (fun acc e => acc + (if e == 0 then DI.one else V[e - 1]!)) DI.zero

/-- `true` = rho L(T*) + L(S+) - L(S-) <= 0 certainly at the variable values V (all lemma conditions certainly hold) -/
def evalVertexN (I : Ids) (fval : Nat) (rho : DI) (V : Array DI) (sp : Split) (L : Nat) : Bool :=
  let P := coordsN I V
  match (List.zipWith (edgeValN I fval V P L) sp.ta.toList sp.tb.toList).mapM id, spDIN I P sp L with
  | some ts, some spl => (rho * ts.foldl (· + ·) DI.zero + spl - smDIN V sp).nonpos
  | _, _ => false

end S43
