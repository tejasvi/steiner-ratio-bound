module

public import S43.Sound.Affine

@[expose] public section

/-! # Network semantics of a split at a point, and its convexity

The checker evaluates, at each vertex, explicit networks: the S+ points are joined by a segment, a star (one Steiner point;
a path through a terminal is the star centred there) or a two-Steiner-point network with the pairing chosen by the lemma id;
Lemma Y2's Psi uses two stars. A *witness* `ω` records those Steiner points. The value
`G = ρ ΣT* + L_net(S+) - L(S-)` and the vertex-checked conditions are convex in `(w, ω)` (`vset_comb`), so a property that
holds at all vertices of a box holds on the box (`S43.Sound.Box`). `bridge` turns the network semantics into the
statement's `certifies`. -/

namespace S43.Stmt

/-- Steiner points of the explicit networks: `x` (S+ star, or the first point of a 4-point network), `y` (second point),
`p1`, `p2` (Psi's two stars) -/
structure Wit where
  x : ℂ
  y : ℂ
  p1 : ℂ
  p2 : ℂ

def Wit.comb (a b : ℝ) (ω₁ ω₂ : Wit) : Wit := ⟨cmb a b ω₁.x ω₂.x, cmb a b ω₁.y ω₂.y, cmb a b ω₁.p1 ω₂.p1, cmb a b ω₁.p2 ω₂.p2⟩

noncomputable def starLen (a b c x : ℂ) : ℝ := dist a x + dist b x + dist c x
noncomputable def pairLen (a b c d x y : ℂ) : ℝ := dist a x + dist b x + dist x y + dist c y + dist d y

/-- Psi with the two SMT terms replaced by explicit stars (a lower bound of `psiY2`) -/
noncomputable def psiNet (w : Vars) (ω : Wit) : ℝ :=
  let p := pts w
  1 + w.b + w.s + 3 * w.d + 2 * w.c + w.e - starLen p.A p.B p.D ω.p1
    - starLen p.D p.Q (p.Q + (2 * w.d + w.c - w.f)) ω.p2 - dist p.Q p.R

/-! ## Term kinds (determined by the split and the lemma id alone) -/

/-- a T* term: a segment between two configuration points, or a lemma bound for a trapped-point edge -/
inductive TermK
  | seg (i j : ℕ)
  | bnd (K : Key)

/-- does lemma `L` give a bound for key `K` (independent of the point) -/
def avail (F : Fam) (L : ℕ) : Key → Bool
  | .Y => true
  | .AX => L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 5 ∨ L = 8
  | .UX => L = 5 ∧ F = .st
  | .VX => L = 5 ∧ F = .st
  | .DX => L = 5 ∧ F = .reg

/-- number of positioned nodes (all but the trapped points X, Y) -/
def nn : Fam → ℕ | .st => 10 | .reg => 8

def tKind (F : Fam) (L : ℕ) (a b : ℕ) : Option TermK :=
  let I := ids F
  if a = I.nX ∨ b = I.nX ∨ a = I.nY ∨ b = I.nY then
    (edgeKey F a b).bind fun K => if avail F L K then some (.bnd K) else none
  else if a < nn F ∧ b < nn F then some (.seg a b) else none

def tKinds (F : Fam) (L : ℕ) (sp : S43.Split) : Option (List TermK) :=
  (List.zipWith (tKind F L) sp.ta.toList sp.tb.toList).mapM id

noncomputable def pt (F : Fam) (w : Vars) (i : ℕ) : ℂ := (nodePt F w i).getD 0

/-- value of a term -/
noncomputable def kVal (F : Fam) (L : ℕ) (w : Vars) : TermK → ℝ
  | .seg i j => dist (pt F w i) (pt F w j)
  | .bnd K => (lemmaBound F L K w).elim 0 (·.2)

/-- condition the checker verifies at every vertex (X lemma conditions; Psi > 0 for Y2 in f_ge_dv) -/
def kVcond (F : Fam) (fval L : ℕ) (w : Vars) (ω : Wit) : TermK → Prop
  | .seg _ _ => True
  | .bnd .Y => (F = .reg ∧ fval = 3) → 0 < psiNet w ω
  | .bnd K => (lemmaBound F L K w).elim False (·.1)

/-- condition that holds at the target point by the subcase (f ≤ d for the lemma-0 Y bound) -/
def kScond (F : Fam) (fval : ℕ) (w : Vars) : TermK → Prop
  | .bnd .Y => ¬ (F = .reg ∧ fval = 3) → w.f ≤ w.d
  | _ => True

/-! ## The S+ network -/

inductive SPK
  | zero
  | seg (i j : ℕ)
  | star (i j k : ℕ)
  | pair (i j k l : ℕ)

def spKind (F : Fam) (L : ℕ) (sp : S43.Split) : Option SPK :=
  let I := ids F
  if !(sp.sp.toList.all (· < nn F)) then none else
  match sp.sp.toList with
  | [] => some .zero
  | [_] => some .zero
  | [a, b] => some (.seg a b)
  | [a, b, c] => some (.star a b c)
  | [a, b, c, d] =>
    if [a, b, c, d] = S43.sorted4 [I.nA, I.nD, I.nQ, I.nR] then
      if L = 3 then some (.pair I.nA I.nR I.nD I.nQ)
      else if L = 4 ∨ L = 7 then some (.pair I.nA I.nD I.nQ I.nR) else none
    else if [a, b, c, d] = S43.sorted4 [I.nB, I.nD, I.nQ, I.nR] then
      if L = 6 then some (.pair I.nB I.nD I.nQ I.nR) else none
    else none
  | _ => none

noncomputable def spVal (F : Fam) (w : Vars) (ω : Wit) : SPK → ℝ
  | .zero => 0
  | .seg i j => dist (pt F w i) (pt F w j)
  | .star i j k => starLen (pt F w i) (pt F w j) (pt F w k) ω.x
  | .pair i j k l => pairLen (pt F w i) (pt F w j) (pt F w k) (pt F w l) ω.x ω.y

/-- the network value `ρ ΣT* + L_net(S+) - L(S-)` -/
noncomputable def gNet (F : Fam) (L : ℕ) (sp : S43.Split) (ρ : ℝ) (ks : List TermK) (sk : SPK) (w : Vars) (ω : Wit) : ℝ :=
  ρ * (ks.map (kVal F L w)).sum + spVal F w ω sk - sMinus F sp w

/-- what the checker establishes at a vertex: nonnegative variables, the vertex-checked conditions, and `gNet ≤ 0` -/
def vset (F : Fam) (fval L : ℕ) (sp : S43.Split) (ρ : ℝ) (ks : List TermK) (sk : SPK) (w : Vars) (ω : Wit) : Prop :=
  (0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d ∧ 0 ≤ w.s ∧ 0 ≤ w.u ∧ 0 ≤ w.v ∧ 0 ≤ w.e ∧ 0 ≤ w.f) ∧
  (∀ t ∈ ks, kVcond F fval L w ω t) ∧ gNet F L sp ρ ks sk w ω ≤ 0

end S43.Stmt

end
