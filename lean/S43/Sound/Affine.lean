import S43.Statements

/-! # Convex combinations of case points and the affine structure of the configuration

`comb a b w₁ w₂` is the convex combination `a w₁ + b w₂` of two variable vectors. All configuration points are affine in the
variables (`pts_comb`), so distances between them, and between them and convex combinations of Steiner points, are convex. -/

namespace S43.Stmt

/-- `a w₁ + b w₂`, coordinatewise -/
def comb (a b : ℝ) (w₁ w₂ : Vars) : Vars :=
  ⟨a * w₁.b + b * w₂.b, a * w₁.c + b * w₂.c, a * w₁.d + b * w₂.d, a * w₁.s + b * w₂.s,
   a * w₁.u + b * w₂.u, a * w₁.v + b * w₂.v, a * w₁.e + b * w₂.e, a * w₁.f + b * w₂.f⟩

/-- `a z₁ + b z₂` for points of the plane -/
def cmb (a b : ℝ) (z₁ z₂ : ℂ) : ℂ := (a : ℂ) * z₁ + (b : ℂ) * z₂

theorem cmb_sub (a b : ℝ) (z₁ z₂ y₁ y₂ : ℂ) : cmb a b z₁ z₂ - cmb a b y₁ y₂ = cmb a b (z₁ - y₁) (z₂ - y₂) := by
  unfold cmb; ring

/-- the norm is convex along `cmb` -/
theorem norm_cmb_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z₁ z₂ : ℂ) : ‖cmb a b z₁ z₂‖ ≤ a * ‖z₁‖ + b * ‖z₂‖ := by
  unfold cmb
  calc ‖(a : ℂ) * z₁ + (b : ℂ) * z₂‖ ≤ ‖(a : ℂ) * z₁‖ + ‖(b : ℂ) * z₂‖ := norm_add_le _ _
    _ = a * ‖z₁‖ + b * ‖z₂‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

theorem dist_cmb_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z₁ z₂ y₁ y₂ : ℂ) :
    dist (cmb a b z₁ z₂) (cmb a b y₁ y₂) ≤ a * dist z₁ y₁ + b * dist z₂ y₂ := by
  unfold dist; rw [cmb_sub]; exact norm_cmb_le ha hb _ _

/-- a constant point is unchanged by a convex combination -/
theorem cmb_const {a b : ℝ} (hab : a + b = 1) (z : ℂ) : cmb a b z z = z := by
  unfold cmb
  have : ((a : ℂ) + (b : ℂ)) = 1 := by exact_mod_cast hab
  linear_combination z * this

/-- every configuration point is affine in the variables -/
theorem pts_comb {a b : ℝ} (hab : a + b = 1) (w₁ w₂ : Vars) :
    pts (comb a b w₁ w₂) =
      { A := cmb a b (pts w₁).A (pts w₂).A, B := cmb a b (pts w₁).B (pts w₂).B, D := cmb a b (pts w₁).D (pts w₂).D,
        U := cmb a b (pts w₁).U (pts w₂).U, V := cmb a b (pts w₁).V (pts w₂).V, P := cmb a b (pts w₁).P (pts w₂).P,
        Q := cmb a b (pts w₁).Q (pts w₂).Q, R := cmb a b (pts w₁).R (pts w₂).R, s := cmb a b (pts w₁).s (pts w₂).s,
        r := cmb a b (pts w₁).r (pts w₂).r } := by
  obtain rfl : b = 1 - a := by linarith
  simp only [pts, comb, cmb, dir0, dir1, dir2]
  congr 1 <;> push_cast <;> ring

end S43.Stmt
