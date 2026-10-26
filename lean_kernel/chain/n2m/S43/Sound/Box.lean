module

public import S43.Sound.Convex

@[expose] public section

/-! # From the vertices to the whole box

`box_of_vertices`: a property of points of `ℝ^n` that is preserved by convex combinations and holds at every vertex of a
box holds on the whole box (induction on the coordinates). `embed` puts the record coordinates of a case into `Vars`
(f := d in the subcase f ≥ d with f eliminated; u = v = 0 for d_regular); it is affine, so the network property
`∃ ω, vset …` transfers from the vertices of a record box to the whole box (`vset_box`). -/

namespace S43.Stmt

/-- `x` with coordinate `k` replaced by `t` -/
def upd {n : ℕ} (x : Fin n → ℝ) (k : Fin n) (t : ℝ) : Fin n → ℝ := Function.update x k t

def combV {n : ℕ} (a b : ℝ) (x y : Fin n → ℝ) : Fin n → ℝ := fun i => a * x i + b * y i

theorem box_of_vertices {n : ℕ} (Pr : (Fin n → ℝ) → Prop) (lo hi : Fin n → ℝ)
    (hcomb : ∀ x y a b, 0 ≤ a → 0 ≤ b → a + b = 1 → Pr x → Pr y → Pr (combV a b x y))
    (hvert : ∀ x : Fin n → ℝ, (∀ i, x i = lo i ∨ x i = hi i) → Pr x) :
    ∀ x : Fin n → ℝ, (∀ i, lo i ≤ x i ∧ x i ≤ hi i) → Pr x := by
  -- induction: points whose coordinates `≥ k` are at an end of their interval satisfy Pr
  have key : ∀ k : ℕ, ∀ x : Fin n → ℝ, (∀ i, lo i ≤ x i ∧ x i ≤ hi i) →
      (∀ i : Fin n, k ≤ i.val → x i = lo i ∨ x i = hi i) → Pr x := by
    intro k
    induction k with
    | zero => intro x _ h; exact hvert x (fun i => h i (Nat.zero_le _))
    | succ k ih =>
      intro x hx hend
      by_cases hk : k < n
      · set kk : Fin n := ⟨k, hk⟩
        -- split x along coordinate k into the two faces
        have hlohi := hx kk
        let xl := upd x kk (lo kk); let xh := upd x kk (hi kk)
        have hxl : Pr xl := by
          apply ih xl
          · intro i; by_cases h : i = kk
            · subst h; simp [xl, upd, hlohi.1, le_trans hlohi.1 hlohi.2]
            · simp [xl, upd, Function.update_of_ne h, hx i]
          · intro i hi'; by_cases h : i = kk
            · subst h; left; simp [xl, upd]
            · simp only [xl, upd, Function.update_of_ne h]
              exact hend i (by
                have : i.val ≠ k := fun e => h (Fin.ext e)
                omega)
        have hxh : Pr xh := by
          apply ih xh
          · intro i; by_cases h : i = kk
            · subst h; simp [xh, upd, hlohi.2, le_trans hlohi.1 hlohi.2]
            · simp [xh, upd, Function.update_of_ne h, hx i]
          · intro i hi'; by_cases h : i = kk
            · subst h; right; simp [xh, upd]
            · simp only [xh, upd, Function.update_of_ne h]
              exact hend i (by
                have : i.val ≠ k := fun e => h (Fin.ext e)
                omega)
        rcases eq_or_lt_of_le (le_trans hlohi.1 hlohi.2) with heq | hlt
        · -- degenerate side: x = xl
          have : x = xl := by
            funext i; by_cases h : i = kk
            · subst h; simp [xl, upd]; linarith [hlohi.1, hlohi.2]
            · simp [xl, upd, Function.update_of_ne h]
          rw [this]; exact hxl
        · -- x = a xl + b xh with a = (hi - x)/(hi - lo), b = (x - lo)/(hi - lo)
          have hd : 0 < hi kk - lo kk := by linarith
          let a := (hi kk - x kk) / (hi kk - lo kk)
          let b := (x kk - lo kk) / (hi kk - lo kk)
          have ha : 0 ≤ a := div_nonneg (by linarith [hlohi.2]) hd.le
          have hb : 0 ≤ b := div_nonneg (by linarith [hlohi.1]) hd.le
          have hab : a + b = 1 := by
            simp only [a, b]; rw [← add_div]; field_simp; ring
          have : x = combV a b xl xh := by
            funext i; simp only [combV]
            by_cases h : i = kk
            · subst h; simp only [xl, xh, upd, Function.update_self, a, b]; field_simp; ring
            · simp only [xl, xh, upd, Function.update_of_ne h]
              have : a * x i + b * x i = (a + b) * x i := by ring
              rw [this, hab, one_mul]
          rw [this]; exact hcomb _ _ _ _ ha hb hab hxl hxh
      · exact ih x hx (fun i hi' => hend i (by have := i.isLt; omega))
  intro x hx
  exact key n x hx (fun i hi' => absurd hi' (by have := i.isLt; omega))

/-! ## Record coordinates -/

/-- box dimension of a case: 8 / 6 variables, one fewer when f := d -/
def nbOf (F : Fam) (fval : ℕ) : ℕ :=
  if fval = 2 then (match F with | .st => 7 | .reg => 5) else (match F with | .st => 8 | .reg => 6)

/-- the record coordinates of a case (in the checker's variable order) as case variables -/
def embed (F : Fam) (fval : ℕ) (x : Fin (nbOf F fval) → ℝ) : Vars :=
  let g := fun (i : ℕ) => if h : i < _ then x ⟨i, h⟩ else 0
  match F with
  | .st => ⟨g 0, g 1, g 2, g 3, g 4, g 5, g 6, if fval = 2 then g 2 else g 7⟩
  | .reg => ⟨g 0, g 1, g 2, g 3, 0, 0, g 4, if fval = 2 then g 2 else g 5⟩

theorem embed_comb (F : Fam) (fval : ℕ) {a b : ℝ} (hab : a + b = 1) (x y) :
    embed F fval (combV a b x y) = comb a b (embed F fval x) (embed F fval y) := by
  cases F <;> simp only [embed, comb, combV] <;> congr 1 <;> (try split_ifs) <;> simp_all

/-- **vertex convex combination**: the network property at every vertex of a record box gives it on the whole box -/
theorem vset_box {F : Fam} {fval L : ℕ} {sp : S43.Split} {ρ : ℝ} (hρ : 0 ≤ ρ) {ks : List TermK} {sk : SPK}
    (lo hi : Fin (nbOf F fval) → ℝ)
    (hv : ∀ x, (∀ i, x i = lo i ∨ x i = hi i) → ∃ ω, vset F fval L sp ρ ks sk (embed F fval x) ω) :
    ∀ x, (∀ i, lo i ≤ x i ∧ x i ≤ hi i) → ∃ ω, vset F fval L sp ρ ks sk (embed F fval x) ω := by
  apply box_of_vertices (fun x => ∃ ω, vset F fval L sp ρ ks sk (embed F fval x) ω) lo hi _ hv
  rintro x y a b ha hb hab ⟨ω₁, h₁⟩ ⟨ω₂, h₂⟩
  refine ⟨Wit.comb a b ω₁ ω₂, ?_⟩
  rw [embed_comb F fval hab]
  exact vset_comb ha hb hab hρ h₁ h₂

end S43.Stmt

end
