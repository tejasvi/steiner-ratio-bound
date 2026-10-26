module

public import Mathlib
public import S43Core.Splits

@[expose] public section

/-! # Statements: the Steiner ratio is at least 2141/2500

Plane = `ℂ` with the Euclidean distance `‖z - w‖`.

* `mstLength P`, `steinerLength P`: lengths of a minimum spanning tree and of a Steiner minimal tree of a finite point set,
  as infima over finite sets of segments that connect `P` (endpoints in `P`, resp. arbitrary).
* `Main.steiner_ratio_ge`: `(2141/2500) * mstLength P ≤ steinerLength P` for every finite `P`, under the named hypotheses
  `LemmaLayer Real` below, for every relation `Real` ("this coordinate vector, with these trapped points, is realized by a
  local configuration of a Steiner minimal tree"); the hypotheses are lemmas of the paper (Sections 2 and
  3), see README.md.
* `Cert.certificate`: the certificate theorem, proved from the certificate data with `native_decide` plus the soundness of the
  checker: every point of the two case domains admits a split from the published lists whose bound is `≤ 0`.

This file states the two theorems with placeholder proofs; `S43Final.lean` proves theorems of the same types and checks the types with `rfl`. -/

namespace S43.Stmt

open Real

/-! ## Spanning trees and Steiner trees -/

/-- total length of a finite set of segments -/
noncomputable def segLength (E : Finset (ℂ × ℂ)) : ℝ := ∑ e ∈ E, ‖e.1 - e.2‖

/-- the graph on `ℂ` whose edges are the segments of `E` -/
def segGraph (E : Finset (ℂ × ℂ)) : SimpleGraph ℂ :=
  SimpleGraph.fromEdgeSet ((fun e : ℂ × ℂ => s(e.1, e.2)) '' (E : Set (ℂ × ℂ)))

/-- the segments `E` connect all points of `P` -/
def Connects (E : Finset (ℂ × ℂ)) (P : Finset ℂ) : Prop := ∀ a ∈ P, ∀ b ∈ P, (segGraph E).Reachable a b

/-- length of a minimum spanning tree: shortest connecting segment set with endpoints in `P` -/
noncomputable def mstLength (P : Finset ℂ) : ℝ :=
  sInf {L | ∃ E : Finset (ℂ × ℂ), (∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ P) ∧ Connects E P ∧ L = segLength E}

/-- length of a Steiner minimal tree: shortest connecting segment set, arbitrary endpoints -/
noncomputable def steinerLength (P : Finset ℂ) : ℝ :=
  sInf {L | ∃ E : Finset (ℂ × ℂ), Connects E P ∧ L = segLength E}

/-! ## The local configurations -/

/-- the two families of the paper: `reg` = d_regular (variables b c d s e f), `st` = d_steiner (b c d s u v e f) -/
inductive Fam | reg | st
  deriving DecidableEq

/-- the case variables; for `reg`, `u` and `v` are not used -/
structure Vars where
  b : ℝ
  c : ℝ
  d : ℝ
  s : ℝ
  u : ℝ
  v : ℝ
  e : ℝ
  f : ℝ

def dir0 : ℂ := 1
noncomputable def dir1 : ℂ := ⟨1 / 2, √3 / 2⟩
noncomputable def dir2 : ℂ := ⟨1 / 2, -(√3 / 2)⟩

/-- the configuration points: A = 0, s = 1, B = s + b dir1, r = s + s dir2, P = r - c dir1, D = r + d dir0,
U = D + u dir1, V = D + v dir2, Q = P + f dir2, R = P - e dir0 (the paper's coordinates; `indep43c.c`, `coords`) -/
structure Pts where
  A : ℂ
  B : ℂ
  D : ℂ
  U : ℂ
  V : ℂ
  P : ℂ
  Q : ℂ
  R : ℂ
  s : ℂ
  r : ℂ

noncomputable def pts (w : Vars) : Pts :=
  let s : ℂ := 1
  let r := s + w.s * dir2
  let P := r - w.c * dir1
  let D := r + w.d * dir0
  { A := 0, B := s + w.b * dir1, D := D, U := D + w.u * dir1, V := D + w.v * dir2, P := P,
    Q := P + w.f * dir2, R := P - w.e * dir0, s := s, r := r }

/-- node ids of the split data (`S43Core.Ids`) to points; the trapped points X, Y have no position here -/
noncomputable def nodePt (F : Fam) (w : Vars) (i : ℕ) : Option ℂ :=
  let p := pts w
  match F with
  | .st => [p.A, p.B, p.D, p.U, p.V, p.P, p.Q, p.R, p.s, p.r][i]?
  | .reg => [p.A, p.B, p.D, p.P, p.Q, p.R, p.s, p.r][i]?

def ids : Fam → S43.Ids | .st => S43.idsSt | .reg => S43.idsReg

/-- the published split lists (numeric form of the authors' splits.txt, see `S43Core.Splits`) -/
def splits : Fam → Array S43.Split | .st => S43.splitsSt | .reg => S43.splitsReg

/-- the case domain: all variables `≥ 0` (for `reg`, `u = v = 0`); for `st` the cherry-swap normal form `max u v ≤ max b 1` -/
def domain (F : Fam) (w : Vars) : Prop :=
  0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d ∧ 0 ≤ w.s ∧ 0 ≤ w.u ∧ 0 ≤ w.v ∧ 0 ≤ w.e ∧ 0 ≤ w.f ∧
  match F with
  | .reg => w.u = 0 ∧ w.v = 0
  | .st => max w.u w.v ≤ max w.b 1

/-! ## Trapped-point bounds (the paper's lemmas 0, 1, 2, 5, 8 and the Y bounds; Lemmas Y2 and X2) -/

/-- which trapped-point distance a T* edge needs -/
inductive Key | AX | UX | VX | DX | Y
  deriving DecidableEq

noncomputable def dist (a b : ℂ) : ℝ := ‖a - b‖
noncomputable def maxdist (a : ℂ) (l : List ℂ) : ℝ := (l.map (dist a)).foldl max 0

/-- Lemma Y2's quantity Psi (d_regular): `1 + b + s + 3d + 2c + e - SMT(A,B,D) - SMT(D,Q,Q*) - |QR|`, `Q* = Q + (2d + c - f)` -/
noncomputable def psiY2 (w : Vars) : ℝ :=
  let p := pts w
  1 + w.b + w.s + 3 * w.d + 2 * w.c + w.e - steinerLength {p.A, p.B, p.D}
    - steinerLength {p.D, p.Q, p.Q + (2 * w.d + w.c - w.f)} - dist p.Q p.R

/-- lemma 5's condition, extended by Lemma X2 -/
noncomputable def cond5 (w : Vars) : Prop :=
  w.e < (2 / √3 - 1) * w.c ∨
  (w.e < w.c ∧ 0 < w.c + w.e + w.f - √(w.e ^ 2 + w.e * w.f + w.f ^ 2) - √3 / 2 * (w.c + w.e))

/-- condition and bound of lemma `L` for key `K` (`none` = the lemma has no bound for this edge) -/
noncomputable def lemmaBound (F : Fam) (L : ℕ) (K : Key) (w : Vars) : Option (Prop × ℝ) :=
  let p := pts w
  match K with
  | .Y =>
    match F with
    | .reg => some (w.f ≤ w.d ∨ 0 < psiY2 w, maxdist p.D [p.P, p.Q])
    | .st => some (w.f ≤ w.d, maxdist p.V [p.r, p.P, p.Q])
  | .AX =>
    match L with
    | 0 => some (w.c ≤ 1, maxdist p.A [p.r, p.P])
    | 1 => some (w.e < 1 - w.c + 2 / √3 * w.s ∧ 1 ≤ w.c + w.e,
                 max (maxdist p.A [p.s, p.r, p.P, p.R]) (√3 / 2 * (w.c + w.e - 1)))
    | 2 => some (w.e < 1 + (2 / √3 - 1) * w.c ∧ 1 ≤ w.c + w.e,
                 max (maxdist p.A [p.s, p.r, p.P, p.R]) (√3 / 2 * (w.c + w.e - 1)))
    | 5 => some (cond5 w, maxdist p.A [p.r, p.P, p.R])
    | 8 => some (w.e < w.s + 1, max (maxdist p.A [p.r, p.P, p.R]) (w.e + w.c - 1))
    | _ => none
  | .UX | .VX | .DX =>
    -- lemma 5 only; (D,X) for d_regular, (U,X) and (V,X) for d_steiner; H = R - ((c - e)/2) dir2
    let W := if K = .UX then p.U else if K = .VX then p.V else p.D
    let H := p.R - ((w.c - w.e) / 2) * dir2
    if L = 5 ∧ ((K = .DX) ↔ F = .reg) then some (cond5 w, max (maxdist W [p.r, p.P, p.R]) (dist W H)) else none

/-- key of a T* edge `(a, b)` that touches a trapped point (`S43.edgeKey`) -/
def edgeKey (F : Fam) (a b : ℕ) : Option Key :=
  (S43.edgeKey (ids F) a b).bind fun
    | .AX => some .AX | .UX => some .UX | .VX => some .VX | .DX => some .DX | .Y => some .Y | _ => none

/-! ## The bound of a split -/

/-- the S- length: edge 0 = (A, s) has length 1, edge `i ≥ 1` has the length of variable `i - 1` -/
noncomputable def varOf (F : Fam) (w : Vars) (i : ℕ) : ℝ :=
  match F with
  | .st => [w.b, w.c, w.d, w.s, w.u, w.v, w.e, w.f].getD i 0
  | .reg => [w.b, w.c, w.d, w.s, w.e, w.f].getD i 0

noncomputable def sMinus (F : Fam) (sp : S43.Split) (w : Vars) : ℝ :=
  (sp.sm.toList.map fun i => if i = 0 then 1 else varOf F w (i - 1)).sum

/-- the S+ length: Steiner minimal tree of the S+ points -/
noncomputable def sPlus (F : Fam) (sp : S43.Split) (w : Vars) : ℝ :=
  steinerLength ((sp.sp.toList.filterMap (nodePt F w)).toFinset)

/-- one T* edge: its length, or the lemma bound (with its condition) when it touches X or Y -/
noncomputable def tEdge (F : Fam) (L : ℕ) (w : Vars) (a b : ℕ) : Option (Prop × ℝ) :=
  let I := ids F
  if a = I.nX ∨ b = I.nX ∨ a = I.nY ∨ b = I.nY then
    (edgeKey F a b).bind fun K => lemmaBound F L K w
  else
    match nodePt F w a, nodePt F w b with
    | some x, some y => some (True, dist x y)
    | _, _ => none

/-- `certifies F sp L ρ w`: every T* edge has a length or a lemma bound whose condition holds at `w`, and
`ρ L(T*) + L(S+) - L(S-) ≤ 0` -/
noncomputable def certifies (F : Fam) (sp : S43.Split) (L : ℕ) (ρ : ℝ) (w : Vars) : Prop :=
  ∃ es : List (Prop × ℝ),
    (List.zipWith (tEdge F L w) sp.ta.toList sp.tb.toList).mapM id = some es ∧
    (∀ e ∈ es, e.1) ∧ ρ * (es.map Prod.snd).sum + sPlus F sp w - sMinus F sp w ≤ 0

/-! ## The certificate theorem (proved in S43Final.lean from the data with native_decide + checker soundness) -/

namespace Cert

theorem certificate (F : Fam) (w : Vars) (hw : domain F w) :
    ∃ sp ∈ splits F, ∃ L ≤ 8, certifies F sp L (2141 / 2500) w := by
  sorry

end Cert

/-! ## The lemma layer as named hypotheses -/

/-- `Real F w X Y`: some Steiner minimal tree contains a local configuration of family `F` with coordinates `w` whose
trapped points are `X` and `Y` (the paper's definitions; any relation can be plugged in, the hypotheses below are what the
proof uses) -/
abbrev Realized := Fam → Vars → ℂ → ℂ → Prop

/-- the trapped-point distance a key bounds -/
noncomputable def keyDist (F : Fam) (K : Key) (w : Vars) (X Y : ℂ) : ℝ :=
  let p := pts w
  match K with
  | .AX => dist p.A X | .UX => dist p.U X | .VX => dist p.V X | .DX => dist p.D X
  | .Y => match F with | .reg => dist p.D Y | .st => dist p.V Y

/-- (H_trap) every lemma bound is valid on realized configurations: published lemmas 0, 1, 2, 5, 8 and the Y bounds,
Lemma X2 (inside `cond5`) and Lemma Y2 (the `0 < psiY2` alternative) -/
def HTrap (Real : Realized) : Prop :=
  ∀ F w X Y L K, Real F w X Y → ∀ cb, lemmaBound F L K w = some cb → cb.1 → keyDist F K w X Y ≤ cb.2

/-- (H_domain) realized coordinates lie in the case domain (cherry swap normal form for `st`) -/
def HDomain (Real : Realized) : Prop := ∀ F w X Y, Real F w X Y → domain F w

/-- the T* length with the true trapped-point distances -/
noncomputable def tTrue (F : Fam) (sp : S43.Split) (w : Vars) (X Y : ℂ) : ℝ :=
  (List.zipWith (fun a b =>
      let I := ids F
      if a = I.nX ∨ b = I.nX ∨ a = I.nY ∨ b = I.nY then
        match edgeKey F a b with | some K => keyDist F K w X Y | none => 0
      else
        match nodePt F w a, nodePt F w b with | some x, some y => dist x y | _, _ => 0)
    sp.ta.toList sp.tb.toList).sum

/-- (H_DuHwang) the Du-Hwang splitting framework with the case reduction and the base cases n ≤ 4: if every realized
configuration has a split from the published lists with `ρ L(T*) + L_SMT(S+) - L(S-) ≤ 0` (true trapped-point
distances, edges to X or Y only through a lemma key), then `ρ L_MST ≤ L_SMT` for every finite point set -/
def HDuHwang (Real : Realized) (ρ : ℝ) : Prop :=
  (∀ F w X Y, Real F w X Y → ∃ sp ∈ splits F,
      (∀ i < sp.ta.size, let a := sp.ta[i]!; let b := sp.tb[i]!; let I := ids F;
        (a = I.nX ∨ b = I.nX ∨ a = I.nY ∨ b = I.nY) → (edgeKey F a b).isSome) ∧
      ρ * tTrue F sp w X Y + sPlus F sp w - sMinus F sp w ≤ 0) →
  ∀ P : Finset ℂ, ρ * mstLength P ≤ steinerLength P

structure LemmaLayer (Real : Realized) : Prop where
  trap : HTrap Real
  domain : HDomain Real
  duHwang : HDuHwang Real (2141 / 2500)

namespace Main

/-- the Steiner ratio is at least 2141/2500, given the lemma layer -/
theorem steiner_ratio_ge (Real : Realized) (H : LemmaLayer Real) :
    ∀ P : Finset ℂ, (2141 / 2500 : ℝ) * mstLength P ≤ steinerLength P := by
  sorry

end Main

end S43.Stmt

end
