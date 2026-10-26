module

public import S43CoreK.DN

@[expose] public section

/-! # Geometry of the kernel checker at one vertex

A line-by-line mirror of lean/'s `S43Core.Geom` / `S43Core.Vertex` on biased-Nat intervals:
the same configuration points (`ptsDI`), distances, angle tests, `smt3n` / `star3` / `pair4`, `maxdist`, the lemma
entries reachable from `edgeKey` (AX, UX, VX, DX, Y), Lemma X2's condition and Lemma Y2's `psiY2PosN`. The only
semantic change: the Steiner points of the explicit networks are computed per vertex by explicit constructions
(Torricelli, Melzak) in fixed-point biased-Nat arithmetic, rounded to the 2^-40 grid, instead of lean/'s
per-vertex Float points. Kernel-shaped: named-field structures instead of
Arrays, helper definitions with arguments instead of `let`s, `Bool` control flow; functions on points take their
arguments apart first (`match`), so that inside one record the kernel shares every point, distance and star between
the vertices that agree on the variables it depends on. -/

namespace S43K
open DN

structure PK where
  x : DN
  y : DN

/-- the variable values at a vertex (`u`, `v` are zero for d_regular; `f = d` in the subcase f >= d with f := d) -/
structure VarsK where
  b : DN
  c : DN
  d : DN
  s : DN
  u : DN
  v : DN
  e : DN
  f : DN

/-- the configuration points (lean/'s `PtsDI`) -/
structure PtsK where
  A : PK
  B : PK
  D : PK
  U : PK
  V : PK
  P : PK
  Q : PK
  R : PK
  s : PK
  r : PK

def PK.zero : PK := ⟨DN.zero, DN.zero⟩
def S0 : PK := ⟨DN.one, DN.zero⟩

/-! ## Points (lean/'s `addDir`, `ptsDI`) -/

/-- lean/'s `addDir src t sgn negT`: `h0 = t/2`, `k0 = h0 SQ3`, negated if `negT`; `(src.x + h, src.y ± k)` -/
def addDirHK (src : PK) (h k : DN) (sgn : Bool) : PK := ⟨add src.x h, bif sgn then add src.y k else sub src.y k⟩
def addDirN (src : PK) (h0 k0 : DN) (sgn negT : Bool) : PK :=
  bif negT then addDirHK src (neg h0) (neg k0) sgn else addDirHK src h0 k0 sgn
def addDirH (src : PK) (h0 : DN) (sgn negT : Bool) : PK := addDirN src h0 (mul h0 SQ3) sgn negT
def addDir (src : PK) (t : DN) (sgn negT : Bool) : PK := addDirH src (half t) sgn negT

/-- the configuration points, each a function of exactly the variables it depends on (so that, inside one record,
the kernel's whnf cache shares a point between all vertices that agree on those variables) -/
def ptr (s : DN) : PK := addDir S0 s false false
def ptP (s c : DN) : PK := addDir (ptr s) c true true
def ptD (s d : DN) : PK := ⟨add (ptr s).x d, (ptr s).y⟩
def ptB (b : DN) : PK := addDir S0 b true false
def ptU (s d u : DN) : PK := addDir (ptD s d) u true false
def ptV (s d v : DN) : PK := addDir (ptD s d) v false false
def ptQ (s c f : DN) : PK := addDir (ptP s c) f false false
def ptR (s c e : DN) : PK := ⟨sub (ptP s c).x e, (ptP s c).y⟩
def ptsV (st : Bool) (b c d s u v e f : DN) : PtsK :=
  ⟨PK.zero, ptB b, ptD s d, bif st then ptU s d u else PK.zero, bif st then ptV s d v else PK.zero,
   ptP s c, ptQ s c f, ptR s c e, S0, ptr s⟩
/-- lean/'s `ptsDI` -/
def ptsK (st : Bool) (W : VarsK) : PtsK := match W with | ⟨b, c, d, s, u, v, e, f⟩ => ptsV st b c d s u v e f

/-! ## Distances, angles, networks -/

def dist2 (dx dy : DN) : DN := sqrt (add (sq dx) (sq dy))
/-- lean/'s `dist` -/
def dist (a b : PK) : DN := match a, b with | ⟨ax, ay⟩, ⟨bx, by_⟩ => dist2 (sub ax bx) (sub ay by_)

def angV2 (ux uy vx vy d : DN) : Bool :=
  bif nonneg d then true else lec (nmul4 (sq d)) (mul (add (sq ux) (sq uy)) (add (sq vx) (sq vy)))
/-- lean/'s `angleLe120Vec` -/
def angleLe120Vec (ux uy vx vy : DN) : Bool := angV2 ux uy vx vy (add (mul ux vx) (mul uy vy))
/-- lean/'s `angleLe120 a b c` (angle at b) -/
def angleLe120 (a b c : PK) : Bool :=
  match a, b, c with | ⟨ax, ay⟩, ⟨bx, by_⟩, ⟨cx, cy⟩ => angleLe120Vec (sub ax bx) (sub ay by_) (sub cx bx) (sub cy by_)

/-! ## Witness points, per vertex (Float-free replacement of lean/'s `fermatW` / `net4W`)

Biased single values (`X = x + B`, scale 2^-100). The Fermat point by the Torricelli construction and the two
Steiner points of a 4-point network by the Melzak construction, at the vertex's own points (their lower ends), rounded
to the 2^-40 grid as lean/'s `ofF`. Any point is admissible: only the interval length evaluation below is rigorous. -/

def addV (X Y : Nat) : Nat := Nat.sub (Nat.add X Y) B
def subV (X Y : Nat) : Nat := Nat.sub (Nat.add X B) Y
def negV (X : Nat) : Nat := Nat.sub B2 X
def mulV (X Y : Nat) : Nat := flZ (prodZ X Y)
def halfV (X : Nat) : Nat := Nat.shiftRight (Nat.add X B) 1
def dbl (X : Nat) : Nat := Nat.sub (Nat.mul 2 X) B
/-- `sqrt 3 / 2` and `1/3` at scale 2^100, biased -/
def S3HB : Nat := 115792089237316195423570985008687907853269984666738381662377822388733014535043
def THIRDB : Nat := 115792089237316195423570985008687907853269984666063114239533660475078697375061
/-- signed quotient `n / d` (`d ≠ 0`) at scale 2^-100, biased -/
def divV (n d : Nat) : Nat := bif Nat.blt d B then qfl (negV n) (Nat.sub B d) else qfl n (Nat.sub d B)
def rnd40 (X : Nat) : Nat := Nat.shiftLeft (Nat.shiftRight (Nat.add X 576460752303423488) 60) 60
/-- clamp to `|v| <= 2^120` (real 2^20), on the 2^-40 grid: any point is admissible, and it keeps every DN value in
range (static bounds) -/
def clampW (X : Nat) : Nat := nmin (nmax X 115792089237316195423570985008687907853268655437644779123584680200852849295360) 115792089237316195423570985008687907853271313893636348955330487814973409984512
def ptW (X Y : Nat) : PK := ⟨⟨clampW (rnd40 X), clampW (rnd40 X)⟩, ⟨clampW (rnd40 Y), clampW (rnd40 Y)⟩⟩

/-- apex of the equilateral triangle on p q on the side opposite to r (lean/'s `apex`: `e1` iff `side r < 0`) -/
def apexE (hx hy sx sy sr : Nat) : Nat × Nat := bif Nat.blt sr B then (subV hx sx, addV hy sy) else (addV hx sx, subV hy sy)
def apexU (px py rx ry ux uy : Nat) : Nat × Nat :=
  apexE (addV px (halfV ux)) (addV py (halfV uy)) (mulV uy S3HB) (mulV ux S3HB)
    (subV (mulV ux (subV ry py)) (mulV uy (subV rx px)))
def apexV (px py qx qy rx ry : Nat) : Nat × Nat := apexU px py rx ry (subV qx px) (subV qy py)

/-- Torricelli: `a + t d1`, `t = ((b - a) × d2) / (d1 × d2)`, `d1 = E_a - a`, `d2 = E_b - b` -/
def torT (ax ay d1x d1y den tn : Nat) : PK :=
  bif Nat.beq den B then ptW ax ay else ptW (addV ax (mulV (divV tn den) d1x)) (addV ay (mulV (divV tn den) d1y))
def torD (ax ay bx by_ d1x d1y d2x d2y : Nat) : PK :=
  torT ax ay d1x d1y (subV (mulV d1x d2y) (mulV d1y d2x)) (subV (mulV (subV bx ax) d2y) (mulV (subV by_ ay) d2x))
def torE (ax ay bx by_ : Nat) (ea eb : Nat × Nat) : PK :=
  torD ax ay bx by_ (subV ea.1 ax) (subV ea.2 ay) (subV eb.1 bx) (subV eb.2 by_)
def torP (ax ay bx by_ cx cy : Nat) : PK := torE ax ay bx by_ (apexV bx by_ cx cy ax ay) (apexV cx cy ax ay bx by_)
/-- the Fermat point of a b c (used where all three angles are certainly <= 120 degrees) -/
def fermatV (a b c : PK) : PK :=
  match a, b, c with | ⟨ax, ay⟩, ⟨bx, by_⟩, ⟨cx, cy⟩ => torP ax.lo ay.lo bx.lo by_.lo cx.lo cy.lo

/-- Melzak: `x = E12 - k1 d`, `y = E34 + k2 d`, `d = E34 - E12`, `k1 = 2 (E12 - C12).d / |d|^2`,
`k2 = 2 (E34 - C34).(-d) / |d|^2`, `C12`, `C34` the centres of the two equilateral triangles -/
def melK (e12 e34 : Nat × Nat) (dx dy dd k1 k2 : Nat) : PK × PK :=
  (ptW (subV e12.1 (mulV k1 dx)) (subV e12.2 (mulV k1 dy)), ptW (addV e34.1 (mulV k2 dx)) (addV e34.2 (mulV k2 dy)))
def melC (e12 e34 : Nat × Nat) (dx dy dd c12x c12y c34x c34y : Nat) : PK × PK :=
  melK e12 e34 dx dy dd
    (divV (dbl (addV (mulV (subV e12.1 c12x) dx) (mulV (subV e12.2 c12y) dy))) dd)
    (divV (dbl (negV (addV (mulV (subV e34.1 c34x) dx) (mulV (subV e34.2 c34y) dy)))) dd)
def melD (p1 p2 p3 p4 : PK) (e12 e34 : Nat × Nat) (dx dy dd : Nat) : PK × PK :=
  bif Nat.beq dd B then
    (ptW (halfV (halfV (addV (addV p1.x.lo p2.x.lo) (addV p3.x.lo p4.x.lo)))) (halfV (halfV (addV (addV p1.y.lo p2.y.lo) (addV p3.y.lo p4.y.lo)))),
     ptW (halfV (halfV (addV (addV p1.x.lo p2.x.lo) (addV p3.x.lo p4.x.lo)))) (halfV (halfV (addV (addV p1.y.lo p2.y.lo) (addV p3.y.lo p4.y.lo)))))
  else melC e12 e34 dx dy dd (mulV (addV (addV p1.x.lo p2.x.lo) e12.1) THIRDB) (mulV (addV (addV p1.y.lo p2.y.lo) e12.2) THIRDB)
    (mulV (addV (addV p3.x.lo p4.x.lo) e34.1) THIRDB) (mulV (addV (addV p3.y.lo p4.y.lo) e34.2) THIRDB)
def melE (p1 p2 p3 p4 : PK) (e12 e34 : Nat × Nat) (dx dy : Nat) : PK × PK :=
  melD p1 p2 p3 p4 e12 e34 dx dy (addV (mulV dx dx) (mulV dy dy))
def melA (p1 p2 p3 p4 : PK) (e12 e34 : Nat × Nat) : PK × PK := melE p1 p2 p3 p4 e12 e34 (subV e34.1 e12.1) (subV e34.2 e12.2)
def melzakF (p1 p2 p3 p4 : PK) : PK × PK :=
  melA p1 p2 p3 p4
    (apexV p1.x.lo p1.y.lo p2.x.lo p2.y.lo (halfV (addV p3.x.lo p4.x.lo)) (halfV (addV p3.y.lo p4.y.lo)))
    (apexV p3.x.lo p3.y.lo p4.x.lo p4.y.lo (halfV (addV p1.x.lo p2.x.lo)) (halfV (addV p1.y.lo p2.y.lo)))

/-- the two Steiner points of the network p1-x, p2-x, x-y, p3-y, p4-y -/
def melzakV (p1 p2 p3 p4 : PK) : PK × PK :=
  match p1, p2, p3, p4 with | ⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩ => melzakF ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨g, h⟩

/-- lean/'s `star3` -/
def star3 (a b c X : PK) : DN := add (add (dist a X) (dist b X)) (dist c X)
def smt3c (a b c : PK) : DN := bif angleLe120 c a b then star3 a b c (fermatV a b c) else add (dist c a) (dist a b)
def smt3b (a b c : PK) : DN := bif angleLe120 b c a then smt3c a b c else add (dist b c) (dist c a)
/-- lean/'s `smt3n` with the star at the Float-free per-vertex Fermat point -/
def smt3K (a b c : PK) : DN := bif angleLe120 a b c then smt3b a b c else add (dist a b) (dist b c)
def pair4XY (p1 p2 p3 p4 : PK) (XY : PK × PK) : DN :=
  add (add (add (add (dist p1 XY.1) (dist p2 XY.1)) (dist XY.1 XY.2)) (dist p3 XY.2)) (dist p4 XY.2)

/-- the angle at b of a b c is >= 120 degrees (on the lower ends, biased single values; a witness choice only) -/
def obtV (ux uy vx vy : Nat) (d : Nat) : Bool :=
  Nat.blt d B && Nat.ble (mulV (addV (mulV ux ux) (mulV uy uy)) (addV (mulV vx vx) (mulV vy vy))) (Nat.sub (Nat.mul 4 (mulV d d)) B3)
def obtU (ux uy vx vy : Nat) : Bool := obtV ux uy vx vy (addV (mulV ux vx) (mulV uy vy))
def obt120 (ax ay bx by_ cx cy : Nat) : Bool := obtU (subV ax bx) (subV ay by_) (subV cx bx) (subV cy by_)
/-- Fermat point allowing degenerate triangles: the vertex with an angle >= 120 degrees, else Torricelli -/
def fermatR3 (ax ay bx by_ cx cy : Nat) : PK :=
  bif obt120 cx cy ax ay bx by_ then ptW ax ay
  else bif obt120 ax ay bx by_ cx cy then ptW bx by_
  else bif obt120 bx by_ cx cy ax ay then ptW cx cy
  else torP ax ay bx by_ cx cy
def fermatR (a b c : PK) : PK :=
  match a, b, c with | ⟨ax, ay⟩, ⟨bx, by_⟩, ⟨cx, cy⟩ => fermatR3 ax.lo ay.lo bx.lo by_.lo cx.lo cy.lo
def cornerW (p : PK) : PK := match p with | ⟨px, py⟩ => ptW px.lo py.lo
/-- the interval with the smaller upper end (the whole interval of one candidate network) -/
def minHi (a b : DN) : DN := bif Nat.ble a.hi b.hi then a else b
/-- lean/'s `net4n` = `pair4` at its numerically optimal points; here the shortest of five explicit candidates: the Melzak
points (full topology) and the degenerate topologies x = p1, x = p2 (y the Fermat point of x, p3, p4) and y = p3, y = p4
(x the Fermat point of p1, p2, y) -/
def pair4K (p1 p2 p3 p4 : PK) : DN :=
  minHi (minHi (minHi (minHi (pair4XY p1 p2 p3 p4 (melzakV p1 p2 p3 p4))
    (pair4XY p1 p2 p3 p4 (cornerW p1, fermatR p1 p3 p4)))
    (pair4XY p1 p2 p3 p4 (cornerW p2, fermatR p2 p3 p4)))
    (pair4XY p1 p2 p3 p4 (fermatR p1 p2 p3, cornerW p3)))
    (pair4XY p1 p2 p3 p4 (fermatR p1 p2 p4, cornerW p4))

/-- lean/'s `maxdist P w [a, b]`, `[a, b, c]`, `[a, b, c, d]` (left fold of `max` from the first distance) -/
def maxd2 (w a b : PK) : DN := max (dist w a) (dist w b)
def maxd3 (w a b c : PK) : DN := max (maxd2 w a b) (dist w c)
def maxd4 (w a b c d : PK) : DN := max (maxd3 w a b c) (dist w d)

/-! ## Lemma conditions and bounds (lean/'s `x2Cond`, `psiY2PosN`, `lemmaEntryN` for the keys `edgeKey` produces) -/

def x2Phi (c e f t : DN) : Bool := pos (sub (sub (add (add c e) f) t) (half (mul (add c e) SQ3)))
def x2Cond2 (c e f : DN) : Bool := bif ltc e c then x2Phi c e f (sqrt (add (add (sq e) (mul e f)) (sq f))) else false
/-- lean/'s `x2Cond` (the variables c, e, f of the vertex) -/
def x2Cond (c e f kc : DN) : Bool := bif ltc e kc then true else x2Cond2 c e f

def psiQs (c d f : DN) (Q : PK) : PK := match Q with | ⟨qx, qy⟩ => ⟨add qx (sub (add (nmul2 d) c) f), qy⟩
def psi0 (b c d s e : DN) : DN := add (add (add (add (add DN.one b) s) (nmul3 d)) (nmul2 c)) e
/-- lean/'s `psiY2PosN` (its two stars at per-vertex Fermat points) -/
def psiY2PosK (b c d s e f : DN) (A Bp D Q R : PK) : Bool :=
  pos (sub (sub (sub (psi0 b c d s e) (smt3K A Bp D)) (smt3K D Q (psiQs c d f Q))) (dist Q R))

/-- trapped-point keys produced by lean/'s `edgeKey` (ADQR / BDQR are not reachable from `edgeKey`) -/
inductive KeyK
  | AX | UX | VX | DX | Y

/-- lean/'s `lemmaEntryN .Y` (`none` = the vertex condition fails) -/
def lemY (st : Bool) (fval : Nat) (b c d s e f : DN) (A Bp D V Pp Q R r : PK) : Option DN :=
  bif Nat.beq fval 3 && !st then (bif psiY2PosK b c d s e f A Bp D Q R then some (maxd2 D Pp Q) else none)
  else bif !(Nat.beq fval 1) then none
  else bif st then some (maxd3 V r Pp Q)
  else some (maxd2 D Pp Q)

def lemAX0 (c : DN) (A r Pp : PK) : Option DN := bif lec c DN.one then some (maxd2 A r Pp) else none
def lemAX12b (e a bb : DN) (A sP r Pp R : PK) : Option DN :=
  bif ltc e a && gec bb DN.one then some (max (maxd4 A sP r Pp R) (half (mul (sub bb DN.one) SQ3))) else none
def lemAX12 (L : Nat) (c e s : DN) (A sP r Pp R : PK) : Option DN :=
  lemAX12b e (bif Nat.beq L 1 then add (sub (nmul2 (divD s SQ3)) c) DN.one else add (mul TWO_OVER_SQ3_M1 c) DN.one)
    (add c e) A sP r Pp R
def lemAX5 (c e f : DN) (A r Pp R : PK) : Option DN :=
  bif x2Cond c e f (mul TWO_OVER_SQ3_M1 c) then some (maxd3 A r Pp R) else none
def lemAX8 (c e s : DN) (A r Pp R : PK) : Option DN :=
  bif ltc e (add s DN.one) then some (max (maxd3 A r Pp R) (sub (add e c) DN.one)) else none
/-- lean/'s `lemmaEntry .AX` for `L ∈ {0, 1, 2, 5, 8}` (other `L`: no entry, decided per record) -/
def lemAX (L : Nat) (c e f s : DN) (A sP r Pp R : PK) : Option DN :=
  bif Nat.beq L 0 then lemAX0 c A r Pp else bif Nat.beq L 5 then lemAX5 c e f A r Pp R
  else bif Nat.beq L 8 then lemAX8 c e s A r Pp R else lemAX12 L c e s A sP r Pp R

def hPt (R : PK) (h : DN) : PK := match R with | ⟨rx, ry⟩ => ⟨sub rx h, add ry (mul h SQ3)⟩
def lemW5b (Wp r Pp R : PK) (h : DN) : Option DN := some (max (maxd3 Wp r Pp R) (dist Wp (hPt R h)))
/-- lean/'s `lemmaEntry .UX/.VX/.DX` at `L = 5` (the point `Wp` = U, V or D) -/
def lemW5 (c e f : DN) (Wp r Pp R : PK) : Option DN :=
  bif x2Cond c e f (mul TWO_OVER_SQ3_M1 c) then lemW5b Wp r Pp R (half (half (sub c e))) else none

def lemmaV (st : Bool) (fval L : Nat) (b c d s e f : DN) (A Bp D U V Pp Q R sP r : PK) : KeyK → Option DN
  | .AX => lemAX L c e f s A sP r Pp R
  | .UX => lemW5 c e f U r Pp R
  | .VX => lemW5 c e f V r Pp R
  | .DX => lemW5 c e f D r Pp R
  | .Y => lemY st fval b c d s e f A Bp D V Pp Q R r
/-- the lemma bound of a trapped-point edge at a vertex (`none` = its condition fails); the variables and points are
taken apart first, so every computation below is built from shared per-variable terms -/
def lemmaK (st : Bool) (fval L : Nat) (W : VarsK) (A Bp D U V Pp Q R sP r : PK) (K : KeyK) : Option DN :=
  match W with | ⟨b, c, d, s, _, _, e, f⟩ => lemmaV st fval L b c d s e f A Bp D U V Pp Q R sP r K

/-- does lemma `L` have an entry for key `K` (lean/'s `none` cases of `lemmaEntry`; = `Stmt.avail`) -/
def availK (st : Bool) (L : Nat) : KeyK → Bool
  | .AX => Nat.beq L 0 || Nat.beq L 1 || Nat.beq L 2 || Nat.beq L 5 || Nat.beq L 8
  | .UX => Nat.beq L 5 && st
  | .VX => Nat.beq L 5 && st
  | .DX => Nat.beq L 5 && !st
  | .Y => true

def nXK (st : Bool) : Nat := bif st then 10 else 8
def nYK (st : Bool) : Nat := bif st then 11 else 9

def edgeKeyX (st : Bool) (o : Nat) : Option KeyK :=
  bif Nat.beq o 0 then some .AX
  else bif st && Nat.beq o 3 then some .UX
  else bif st && Nat.beq o 4 then some .VX
  else bif !st && Nat.beq o 2 then some .DX
  else none
def edgeKey2 (st : Bool) (o imp : Nat) : Option KeyK :=
  bif Nat.beq imp (nXK st) then edgeKeyX st o
  else bif Nat.beq imp (nYK st) then (bif Nat.beq o (bif st then 4 else 2) then some .Y else none)
  else none
/-- lean/'s `edgeKey` -/
def edgeKeyK (st : Bool) (a b : Nat) : Option KeyK :=
  bif Nat.beq a (nXK st) || Nat.beq a (nYK st) then edgeKey2 st b a else edgeKey2 st a b

end S43K

end
