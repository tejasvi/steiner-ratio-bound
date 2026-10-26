module

public import S43CoreK.GeomK

@[expose] public section

/-! # The vertex evaluation of the kernel checker

Mirror of lean/'s `evalVertexN` (`S43Core.Vertex`) in the kernel-native types. The T* terms and the S+ kind depend on the split
and the lemma id only, so they are computed by `tKindsK` / `spKindK` (lean/'s `tKinds` / `spKind` with `edgeKey` and
`avail`); inside one record these are the same closed terms at every vertex, so the kernel evaluates them once. At a
vertex: the configuration points, the T* sum in lean/'s order, the S+ value at per-vertex witness points, the S- sum, and the
certain test `rho ΣT* + L(S+) - L(S-) <= 0`. -/

namespace S43K
open DN

/-- a split with lists (lean/'s `Split`: S- edge codes, S+ node ids, T* edges, monotone mask) -/
structure SplitK where
  sm : List Nat
  sp : List Nat
  ta : List Nat
  tb : List Nat
  mono : Nat

/-- a T* term (lean/'s `Stmt.TermK`) -/
inductive TK
  | seg (i j : Nat)
  | bnd (K : KeyK)

/-- the S+ network (lean/'s `Stmt.SPK`) -/
inductive SK
  | zero
  | seg (i j : Nat)
  | star (i j k : Nat)
  | pair (i j k l : Nat)

def tKindX (st : Bool) (L : Nat) : Option KeyK → Option TK
  | none => none
  | some K => bif availK st L K then some (.bnd K) else none
/-- lean/'s `tKind` -/
def tKindK (st : Bool) (L a b : Nat) : Option TK :=
  bif Nat.beq a (nXK st) || Nat.beq b (nXK st) || Nat.beq a (nYK st) || Nat.beq b (nYK st) then
    tKindX st L (edgeKeyK st a b)
  else bif Nat.blt a (nXK st) && Nat.blt b (nXK st) then some (.seg a b) else none

def consT : Option TK → Option (List TK) → Option (List TK)
  | some t, some ts => some (t :: ts)
  | _, _ => none
/-- lean/'s `tKinds` = `(List.zipWith (tKind F L) ta tb).mapM id` -/
def tKindsK (st : Bool) (L : Nat) : List Nat → List Nat → Option (List TK)
  | a :: as, b :: bs => consT (tKindK st L a b) (tKindsK st L as bs)
  | _, _ => some []

def allLt (n : Nat) : List Nat → Bool
  | [] => true
  | a :: as => Nat.blt a n && allLt n as

def eq4 (a b c d a' b' c' d' : Nat) : Bool := Nat.beq a a' && Nat.beq b b' && Nat.beq c c' && Nat.beq d d'
/-- the pairing of a 4-point S+ by lemma id (lean/'s `spDIN` / `spKind`): ids A D Q R (or B D Q R) of the family -/
def spKind4 (st : Bool) (L a b c d : Nat) : Option SK :=
  bif (bif st then eq4 a b c d 0 2 6 7 else eq4 a b c d 0 2 4 5) then
    (bif Nat.beq L 3 then some (bif st then .pair 0 7 2 6 else .pair 0 5 2 4)
     else bif Nat.beq L 4 || Nat.beq L 7 then some (bif st then .pair 0 2 6 7 else .pair 0 2 4 5) else none)
  else bif (bif st then eq4 a b c d 1 2 6 7 else eq4 a b c d 1 2 4 5) then
    (bif Nat.beq L 6 then some (bif st then .pair 1 2 6 7 else .pair 1 2 4 5) else none)
  else none
def spKindL (st : Bool) (L : Nat) : List Nat → Option SK
  | [] => some .zero
  | [_] => some .zero
  | [a, b] => some (.seg a b)
  | [a, b, c] => some (.star a b c)
  | [a, b, c, d] => spKind4 st L a b c d
  | _ => none
/-- lean/'s `spKind` -/
def spKindK (st : Bool) (L : Nat) (sp : List Nat) : Option SK :=
  bif allLt (nXK st) sp then spKindL st L sp else none

/-! ## At a vertex -/

/-- variable by index (d_steiner: b c d s u v e f; d_regular: b c d s e f; else 0, as lean/'s `V[j]!`) -/
def varK (st : Bool) (W : VarsK) (j : Nat) : DN :=
  bif Nat.ble j 3 then
    (bif Nat.ble j 1 then (bif Nat.beq j 0 then W.b else W.c) else bif Nat.beq j 2 then W.d else W.s)
  else bif st then
    (bif Nat.beq j 4 then W.u else bif Nat.beq j 5 then W.v else bif Nat.beq j 6 then W.e else bif Nat.beq j 7 then W.f
     else DN.zero)
  else bif Nat.beq j 4 then W.e else bif Nat.beq j 5 then W.f else DN.zero

/-- point by node id from the taken-apart points (d_steiner: A B D U V P Q R s r = 0..9; d_regular: A B D P Q R s r =
0..7; else the origin, as lean/'s `coordsN` for the unpositioned X, Y) -/
def ptSel (st : Bool) (i : Nat) (A Bp D U V Pp Q R sP r : PK) : PK :=
  bif st then
    (bif Nat.ble i 4 then
      (bif Nat.ble i 1 then (bif Nat.beq i 0 then A else Bp) else bif Nat.beq i 2 then D else bif Nat.beq i 3 then U else V)
     else bif Nat.ble i 7 then (bif Nat.beq i 5 then Pp else bif Nat.beq i 6 then Q else R)
     else bif Nat.beq i 8 then sP else bif Nat.beq i 9 then r else PK.zero)
  else
    (bif Nat.ble i 3 then
      (bif Nat.ble i 1 then (bif Nat.beq i 0 then A else Bp) else bif Nat.beq i 2 then D else Pp)
     else bif Nat.ble i 5 then (bif Nat.beq i 4 then Q else R)
     else bif Nat.beq i 6 then sP else bif Nat.beq i 7 then r else PK.zero)

def termValK (st : Bool) (fval L : Nat) (W : VarsK) (A Bp D U V Pp Q R sP r : PK) : TK → Option DN
  | .seg i j => some (dist (ptSel st i A Bp D U V Pp Q R sP r) (ptSel st j A Bp D U V Pp Q R sP r))
  | .bnd K => lemmaK st fval L W A Bp D U V Pp Q R sP r K

/-- the T* sum, left to right from 0 (lean/'s `ts.foldl (· + ·) DI.zero` after `mapM`) -/
def sumTs (st : Bool) (fval L : Nat) (W : VarsK) (A Bp D U V Pp Q R sP r : PK) : List TK → DN → Option DN
  | [], acc => some acc
  | t :: ts, acc =>
    match termValK st fval L W A Bp D U V Pp Q R sP r t with
    | some z => sumTs st fval L W A Bp D U V Pp Q R sP r ts (add acc z)
    | none => none

/-- lean/'s `spDIN` value for a valid kind -/
def spValK (st : Bool) (A Bp D U V Pp Q R sP r : PK) : SK → DN
  | .zero => DN.zero
  | .seg i j => dist (ptSel st i A Bp D U V Pp Q R sP r) (ptSel st j A Bp D U V Pp Q R sP r)
  | .star i j k => smt3K (ptSel st i A Bp D U V Pp Q R sP r) (ptSel st j A Bp D U V Pp Q R sP r) (ptSel st k A Bp D U V Pp Q R sP r)
  | .pair i j k l => pair4K (ptSel st i A Bp D U V Pp Q R sP r) (ptSel st j A Bp D U V Pp Q R sP r)
      (ptSel st k A Bp D U V Pp Q R sP r) (ptSel st l A Bp D U V Pp Q R sP r)

/-- lean/'s `smDIN` (left fold from 0; code 0 = the unit edge (A, s), code e >= 1 = variable e-1) -/
def smSum (st : Bool) (W : VarsK) : List Nat → DN → DN
  | [], acc => acc
  | e :: es, acc => smSum st W es (add acc (bif Nat.beq e 0 then DN.one else varK st W (Nat.sub e 1)))

def finV (t spl sm : DN) : Bool := nonpos (sub (add (mul RHO t) spl) sm)
def evalPlan3 (st : Bool) (fval L : Nat) (W : VarsK) (A Bp D U V Pp Q R sP r : PK) (ts : List TK) (sk : SK)
    (sm : List Nat) : Bool :=
  match sumTs st fval L W A Bp D U V Pp Q R sP r ts DN.zero with
  | some t => finV t (spValK st A Bp D U V Pp Q R sP r sk) (smSum st W sm DN.zero)
  | none => false
def evalPlan2 (st : Bool) (fval L : Nat) (W : VarsK) (P : PtsK) (ts : List TK) (sk : SK) (sm : List Nat) : Bool :=
  match P with | ⟨A, Bp, D, U, V, Pp, Q, R, sP, r⟩ => evalPlan3 st fval L W A Bp D U V Pp Q R sP r ts sk sm

/-- `true` = `rho L(T*) + L(S+) - L(S-) <= 0` certainly at the vertex values `W` and all vertex conditions hold
(lean/'s `evalVertexN` with Float-free per-vertex witness points) -/
def evalVertexK (st : Bool) (fval L : Nat) (W : VarsK) (sp : SplitK) : Bool :=
  match tKindsK st L sp.ta sp.tb, spKindK st L sp.sp with
  | some ts, some sk => evalPlan2 st fval L W (ptsK st W) ts sk sp.sm
  | _, _ => false

end S43K

end
