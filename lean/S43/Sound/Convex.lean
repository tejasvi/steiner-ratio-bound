import S43.Sound.Net

/-! # The vertex set is convex

`vset_comb`: if the network semantics holds at `(w₁, ω₁)` and `(w₂, ω₂)`, it holds at the convex combination. Every term is a
norm of an affine function of `(w, ω)` (or a maximum of such and affine terms), the S- length is affine, the X-lemma
conditions are linear or (lemma 5 with Lemma X2) a convex region, and Psi is concave. -/

namespace S43.Stmt

variable {a b : ℝ}

theorem comb_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ a * x + b * y := by positivity

theorem max_le_comb (ha : 0 ≤ a) (hb : 0 ≤ b) {x y x₁ y₁ x₂ y₂ : ℝ} (hx : x ≤ a * x₁ + b * x₂) (hy : y ≤ a * y₁ + b * y₂) :
    max x y ≤ a * max x₁ y₁ + b * max x₂ y₂ := by
  have h1 : a * x₁ ≤ a * max x₁ y₁ := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
  have h2 : b * x₂ ≤ b * max x₂ y₂ := mul_le_mul_of_nonneg_left (le_max_left _ _) hb
  have h3 : a * y₁ ≤ a * max x₁ y₁ := mul_le_mul_of_nonneg_left (le_max_right _ _) ha
  have h4 : b * y₂ ≤ b * max x₂ y₂ := mul_le_mul_of_nonneg_left (le_max_right _ _) hb
  exact max_le (by linarith) (by linarith)

theorem zero_le_comb' (hab : a + b = 1) : (0 : ℝ) ≤ a * 0 + b * 0 := by simp

theorem cmb_zero (a b : ℝ) : cmb a b 0 0 = 0 := by simp [cmb]

theorem pt_comb (hab : a + b = 1) (F : Fam) (w₁ w₂ : Vars) (i : ℕ) :
    pt F (comb a b w₁ w₂) i = cmb a b (pt F w₁ i) (pt F w₂ i) := by
  unfold pt nodePt
  rw [pts_comb hab]
  cases F
  · by_cases hi : i < 8
    · interval_cases i <;> simp
    · push_neg at hi
      have h1 : ∀ (l : List ℂ), l.length = 8 → l[i]? = none := fun l hl => List.getElem?_eq_none (by omega)
      dsimp only
      rw [h1 _ (by simp), h1 _ (by simp), h1 _ (by simp)]; simp [cmb_zero]
  · by_cases hi : i < 10
    · interval_cases i <;> simp
    · push_neg at hi
      have h1 : ∀ (l : List ℂ), l.length = 10 → l[i]? = none := fun l hl => List.getElem?_eq_none (by omega)
      dsimp only
      rw [h1 _ (by simp), h1 _ (by simp), h1 _ (by simp)]; simp [cmb_zero]

theorem dist_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (z₁ z₂ y₁ y₂ : ℂ) :
    dist (cmb a b z₁ z₂) (cmb a b y₁ y₂) ≤ a * dist z₁ y₁ + b * dist z₂ y₂ := dist_cmb_le ha hb _ _ _ _

theorem maxdist_cons_le (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (x₁ x₂ : ℂ) :
    ∀ (l₁ l₂ : List ℂ), l₁.length = l₂.length →
      maxdist (cmb a b x₁ x₂) (List.zipWith (cmb a b) l₁ l₂) ≤ a * maxdist x₁ l₁ + b * maxdist x₂ l₂ := by
  -- generalize the accumulator of the fold
  have key : ∀ (l₁ l₂ : List ℂ) (m m₁ m₂ : ℝ), l₁.length = l₂.length → m ≤ a * m₁ + b * m₂ →
      ((List.zipWith (cmb a b) l₁ l₂).map (dist (cmb a b x₁ x₂))).foldl max m ≤
        a * (l₁.map (dist x₁)).foldl max m₁ + b * (l₂.map (dist x₂)).foldl max m₂ := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ m m₁ m₂ hl hm; cases l₂ <;> simp_all
    | cons y₁ t₁ ih =>
      intro l₂ m m₁ m₂ hl hm
      cases l₂ with
      | nil => simp at hl
      | cons y₂ t₂ =>
        simp only [List.zipWith_cons_cons, List.map_cons, List.foldl_cons]
        exact ih t₂ _ _ _ (by simpa using hl) (max_le_comb ha hb hm (dist_comb ha hb _ _ _ _))
  intro l₁ l₂ hl
  unfold maxdist
  exact key l₁ l₂ 0 0 0 hl (by simp)

theorem lin_comb (hab : a + b = 1) (x₁ x₂ : ℝ) (k c : ℝ) :
    k * ((a * x₁ + b * x₂) + c) = a * (k * (x₁ + c)) + b * (k * (x₂ + c)) := by
  obtain rfl : b = 1 - a := by linarith
  ring

/-- the lemma-bound value is convex in the variables -/
theorem bound_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (F : Fam) (L : ℕ) (K : Key) (w₁ w₂ : Vars) :
    (lemmaBound F L K (comb a b w₁ w₂)).elim 0 (·.2) ≤
      a * (lemmaBound F L K w₁).elim 0 (·.2) + b * (lemmaBound F L K w₂).elim 0 (·.2) := by
  have md := fun (x₁ x₂ : ℂ) (l₁ l₂ : List ℂ) (h : l₁.length = l₂.length) => maxdist_cons_le ha hb hab x₁ x₂ l₁ l₂ h
  have hb' : b = 1 - a := by linarith
  unfold lemmaBound
  rw [pts_comb hab]
  cases K
  · -- AX
    rcases L with _ | _ | _ | _ | _ | _ | _ | _ | _ | L
    · simpa using md (pts w₁).A (pts w₂).A [(pts w₁).r, (pts w₁).P] [(pts w₂).r, (pts w₂).P] rfl
    · simp only [Option.elim]
      refine max_le_comb ha hb ?_ ?_
      · simpa using md (pts w₁).A (pts w₂).A [(pts w₁).s, (pts w₁).r, (pts w₁).P, (pts w₁).R]
          [(pts w₂).s, (pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
      · simp only [comb]; subst hb'; ring_nf; rfl
    · simp only [Option.elim]
      refine max_le_comb ha hb ?_ ?_
      · simpa using md (pts w₁).A (pts w₂).A [(pts w₁).s, (pts w₁).r, (pts w₁).P, (pts w₁).R]
          [(pts w₂).s, (pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
      · simp only [comb]; subst hb'; ring_nf; rfl
    · simp
    · simp
    · simpa using md (pts w₁).A (pts w₂).A [(pts w₁).r, (pts w₁).P, (pts w₁).R] [(pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
    · simp
    · simp
    · simp only [Option.elim]
      refine max_le_comb ha hb ?_ ?_
      · simpa using md (pts w₁).A (pts w₂).A [(pts w₁).r, (pts w₁).P, (pts w₁).R] [(pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
      · simp only [comb]; subst hb'; ring_nf; rfl
    · simp
  · -- UX
    simp only [reduceCtorEq, ↓reduceIte]
    split_ifs with h
    · simp only [Option.elim]
      refine max_le_comb ha hb ?_ ?_
      · simpa using md (pts w₁).U (pts w₂).U [(pts w₁).r, (pts w₁).P, (pts w₁).R] [(pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
      · have hH : (cmb a b (pts w₁).R (pts w₂).R) - (((comb a b w₁ w₂).c : ℂ) - ((comb a b w₁ w₂).e : ℂ)) / 2 * dir2 =
            cmb a b ((pts w₁).R - ((w₁.c : ℂ) - (w₁.e : ℂ)) / 2 * dir2) ((pts w₂).R - ((w₂.c : ℂ) - (w₂.e : ℂ)) / 2 * dir2) := by
          simp only [cmb, comb]; subst hb'; push_cast; ring
        rw [hH]; exact dist_comb ha hb _ _ _ _
    · simp
  · -- VX
    simp only [reduceCtorEq, ↓reduceIte]
    split_ifs with h
    · simp only [Option.elim]
      refine max_le_comb ha hb ?_ ?_
      · simpa using md (pts w₁).V (pts w₂).V [(pts w₁).r, (pts w₁).P, (pts w₁).R] [(pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
      · have hH : (cmb a b (pts w₁).R (pts w₂).R) - (((comb a b w₁ w₂).c : ℂ) - ((comb a b w₁ w₂).e : ℂ)) / 2 * dir2 =
            cmb a b ((pts w₁).R - ((w₁.c : ℂ) - (w₁.e : ℂ)) / 2 * dir2) ((pts w₂).R - ((w₂.c : ℂ) - (w₂.e : ℂ)) / 2 * dir2) := by
          simp only [cmb, comb]; subst hb'; push_cast; ring
        rw [hH]; exact dist_comb ha hb _ _ _ _
    · simp
  · -- DX
    simp only [reduceCtorEq, ↓reduceIte]
    split_ifs with h
    · simp only [Option.elim]
      refine max_le_comb ha hb ?_ ?_
      · simpa using md (pts w₁).D (pts w₂).D [(pts w₁).r, (pts w₁).P, (pts w₁).R] [(pts w₂).r, (pts w₂).P, (pts w₂).R] rfl
      · have hH : (cmb a b (pts w₁).R (pts w₂).R) - (((comb a b w₁ w₂).c : ℂ) - ((comb a b w₁ w₂).e : ℂ)) / 2 * dir2 =
            cmb a b ((pts w₁).R - ((w₁.c : ℂ) - (w₁.e : ℂ)) / 2 * dir2) ((pts w₂).R - ((w₂.c : ℂ) - (w₂.e : ℂ)) / 2 * dir2) := by
          simp only [cmb, comb]; subst hb'; push_cast; ring
        rw [hH]; exact dist_comb ha hb _ _ _ _
    · simp
  · -- Y
    cases F
    · simpa using md (pts w₁).D (pts w₂).D [(pts w₁).P, (pts w₁).Q] [(pts w₂).P, (pts w₂).Q] rfl
    · simpa using md (pts w₁).V (pts w₂).V [(pts w₁).r, (pts w₁).P, (pts w₁).Q] [(pts w₂).r, (pts w₂).P, (pts w₂).Q] rfl

/-! ## Conditions -/

theorem comb_lt (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {x₁ x₂ y₁ y₂ : ℝ} (h₁ : x₁ < y₁) (h₂ : x₂ < y₂) :
    a * x₁ + b * x₂ < a * y₁ + b * y₂ := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; simp at hab; subst hab; simpa using h₂
  · nlinarith [mul_le_mul_of_nonneg_left h₂.le hb]

theorem comb_le (ha : 0 ≤ a) (hb : 0 ≤ b) {x₁ x₂ y₁ y₂ : ℝ} (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂) :
    a * x₁ + b * x₂ ≤ a * y₁ + b * y₂ := by nlinarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb]

/-- `√(e² + ef + f²)` is the norm of a linear image of `(e, f)` -/
theorem sqrt_ef (e f : ℝ) : √(e ^ 2 + e * f + f ^ 2) = ‖(⟨e + f / 2, √3 / 2 * f⟩ : ℂ)‖ := by
  rw [Complex.norm_def, Complex.normSq_mk]
  congr 1
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  nlinarith [h3]

noncomputable def phiX (w : Vars) : ℝ :=
  w.c + w.e + w.f - √(w.e ^ 2 + w.e * w.f + w.f ^ 2) - √3 / 2 * (w.c + w.e)

theorem phiX_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (w₁ w₂ : Vars) :
    a * phiX w₁ + b * phiX w₂ ≤ phiX (comb a b w₁ w₂) := by
  have hn : √((comb a b w₁ w₂).e ^ 2 + (comb a b w₁ w₂).e * (comb a b w₁ w₂).f + (comb a b w₁ w₂).f ^ 2) ≤
      a * √(w₁.e ^ 2 + w₁.e * w₁.f + w₁.f ^ 2) + b * √(w₂.e ^ 2 + w₂.e * w₂.f + w₂.f ^ 2) := by
    rw [sqrt_ef, sqrt_ef, sqrt_ef]
    have : (⟨(comb a b w₁ w₂).e + (comb a b w₁ w₂).f / 2, √3 / 2 * (comb a b w₁ w₂).f⟩ : ℂ) =
        cmb a b ⟨w₁.e + w₁.f / 2, √3 / 2 * w₁.f⟩ ⟨w₂.e + w₂.f / 2, √3 / 2 * w₂.f⟩ := by
      apply Complex.ext <;> simp [cmb, comb] <;> ring
    rw [this]; exact norm_cmb_le ha hb _ _
  have hb' : b = 1 - a := by linarith
  unfold phiX
  simp only [comb] at hn ⊢
  subst hb'
  nlinarith [hn]

/-- lemma 5's condition with Lemma X2 is the convex region `e < c ∧ Phi_X > 0` (for nonnegative variables) -/
theorem cond5_iff (w : Vars) (hc : 0 ≤ w.c) (he : 0 ≤ w.e) (hf : 0 ≤ w.f) :
    cond5 w ↔ (w.e < w.c ∧ 0 < phiX w) := by
  unfold cond5
  constructor
  · rintro (h | h)
    · have hs3 : √3 < 2 := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hs3' : 1 < √3 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have hpos : 0 < √3 := by linarith
      have hk : 2 / √3 - 1 < 1 := by rw [div_sub_one hpos.ne', div_lt_one hpos]; linarith
      have hk0 : 0 < 2 / √3 - 1 := by rw [sub_pos, lt_div_iff₀ hpos]; linarith
      have hcpos : 0 < w.c := by
        by_contra hcn; push_neg at hcn
        have : (2 / √3 - 1) * w.c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le hcn
        linarith
      refine ⟨by nlinarith, ?_⟩
      -- √(e² + ef + f²) ≤ e + f, so Phi_X ≥ (1 - √3/2) c - (√3/2) e > 0
      have hsq : √(w.e ^ 2 + w.e * w.f + w.f ^ 2) ≤ w.e + w.f := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith
      unfold phiX
      have h2 : w.e * √3 < (2 - √3) * w.c := by
        have := h; rw [div_sub_one hpos.ne'] at this
        rw [div_mul_eq_mul_div, lt_div_iff₀ hpos] at this
        linarith
      nlinarith [hsq, h2]
    · exact ⟨h.1, by unfold phiX; linarith [h.2]⟩
  · rintro ⟨h1, h2⟩; right; exact ⟨h1, by unfold phiX at h2; linarith⟩

theorem cond5_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (w₁ w₂ : Vars)
    (n₁ : 0 ≤ w₁.c ∧ 0 ≤ w₁.e ∧ 0 ≤ w₁.f) (n₂ : 0 ≤ w₂.c ∧ 0 ≤ w₂.e ∧ 0 ≤ w₂.f)
    (h₁ : cond5 w₁) (h₂ : cond5 w₂) : cond5 (comb a b w₁ w₂) := by
  rw [cond5_iff w₁ n₁.1 n₁.2.1 n₁.2.2] at h₁
  rw [cond5_iff w₂ n₂.1 n₂.2.1 n₂.2.2] at h₂
  have nc : 0 ≤ (comb a b w₁ w₂).c := by simp only [comb]; exact comb_nonneg ha hb n₁.1 n₂.1
  have ne : 0 ≤ (comb a b w₁ w₂).e := by simp only [comb]; exact comb_nonneg ha hb n₁.2.1 n₂.2.1
  have nf : 0 ≤ (comb a b w₁ w₂).f := by simp only [comb]; exact comb_nonneg ha hb n₁.2.2 n₂.2.2
  rw [cond5_iff _ nc ne nf]
  refine ⟨?_, ?_⟩
  · simp only [comb]; exact comb_lt ha hb hab h₁.1 h₂.1
  · have := phiX_comb ha hb hab w₁ w₂
    have := comb_lt ha hb hab h₁.2 h₂.2
    simp at this; linarith

/-- an X-lemma condition (the statement's) is preserved by convex combinations of nonnegative points -/
theorem xcond_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (F : Fam) (L : ℕ) (K : Key) (hK : K ≠ .Y)
    (w₁ w₂ : Vars) (n₁ : 0 ≤ w₁.c ∧ 0 ≤ w₁.e ∧ 0 ≤ w₁.f) (n₂ : 0 ≤ w₂.c ∧ 0 ≤ w₂.e ∧ 0 ≤ w₂.f)
    (h₁ : (lemmaBound F L K w₁).elim False (·.1)) (h₂ : (lemmaBound F L K w₂).elim False (·.1)) :
    (lemmaBound F L K (comb a b w₁ w₂)).elim False (·.1) := by
  have hb' : b = 1 - a := by linarith
  cases K
  · unfold lemmaBound at h₁ h₂ ⊢
    rcases L with _ | _ | _ | _ | _ | _ | _ | _ | _ | L
    · simp only [Option.elim] at h₁ h₂ ⊢; simp only [comb]; nlinarith
    · simp only [Option.elim] at h₁ h₂ ⊢; simp only [comb]
      exact ⟨by have := comb_lt ha hb hab h₁.1 h₂.1; subst hb'; nlinarith, by subst hb'; nlinarith [h₁.2, h₂.2]⟩
    · simp only [Option.elim] at h₁ h₂ ⊢; simp only [comb]
      exact ⟨by have := comb_lt ha hb hab h₁.1 h₂.1; subst hb'; nlinarith, by subst hb'; nlinarith [h₁.2, h₂.2]⟩
    · simp at h₁
    · simp at h₁
    · simp only [Option.elim] at h₁ h₂ ⊢; exact cond5_comb ha hb hab w₁ w₂ n₁ n₂ h₁ h₂
    · simp at h₁
    · simp at h₁
    · simp only [Option.elim] at h₁ h₂ ⊢; simp only [comb]
      have := comb_lt ha hb hab h₁ h₂; subst hb'; nlinarith
    · simp at h₁
  all_goals first
    | exact absurd rfl hK
    | (unfold lemmaBound at h₁ h₂ ⊢
       simp only [reduceCtorEq, ↓reduceIte] at h₁ h₂ ⊢
       split_ifs at h₁ h₂ ⊢ with h
       · simp only [Option.elim] at h₁ h₂ ⊢; exact cond5_comb ha hb hab w₁ w₂ n₁ n₂ h₁ h₂
       · simp at h₁)

/-! ## Psi, the S+ network, the S- length -/

theorem starLen_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (a₁ b₁ c₁ x₁ a₂ b₂ c₂ x₂ : ℂ) :
    starLen (cmb a b a₁ a₂) (cmb a b b₁ b₂) (cmb a b c₁ c₂) (cmb a b x₁ x₂) ≤
      a * starLen a₁ b₁ c₁ x₁ + b * starLen a₂ b₂ c₂ x₂ := by
  unfold starLen
  have := dist_comb ha hb a₁ a₂ x₁ x₂; have := dist_comb ha hb b₁ b₂ x₁ x₂; have := dist_comb ha hb c₁ c₂ x₁ x₂
  linarith

theorem pairLen_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (a₁ b₁ c₁ d₁ x₁ y₁ a₂ b₂ c₂ d₂ x₂ y₂ : ℂ) :
    pairLen (cmb a b a₁ a₂) (cmb a b b₁ b₂) (cmb a b c₁ c₂) (cmb a b d₁ d₂) (cmb a b x₁ x₂) (cmb a b y₁ y₂) ≤
      a * pairLen a₁ b₁ c₁ d₁ x₁ y₁ + b * pairLen a₂ b₂ c₂ d₂ x₂ y₂ := by
  unfold pairLen
  have := dist_comb ha hb a₁ a₂ x₁ x₂; have := dist_comb ha hb b₁ b₂ x₁ x₂; have := dist_comb ha hb x₁ x₂ y₁ y₂
  have := dist_comb ha hb c₁ c₂ y₁ y₂; have := dist_comb ha hb d₁ d₂ y₁ y₂
  linarith

theorem psiNet_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (w₁ w₂ : Vars) (ω₁ ω₂ : Wit) :
    a * psiNet w₁ ω₁ + b * psiNet w₂ ω₂ ≤ psiNet (comb a b w₁ w₂) (Wit.comb a b ω₁ ω₂) := by
  have hb' : b = 1 - a := by linarith
  unfold psiNet
  rw [pts_comb hab]
  simp only [Wit.comb]
  have hq : (cmb a b (pts w₁).Q (pts w₂).Q) + (((2 * (comb a b w₁ w₂).d + (comb a b w₁ w₂).c - (comb a b w₁ w₂).f : ℝ)) : ℂ) =
      cmb a b ((pts w₁).Q + ((2 * w₁.d + w₁.c - w₁.f : ℝ) : ℂ)) ((pts w₂).Q + ((2 * w₂.d + w₂.c - w₂.f : ℝ) : ℂ)) := by
    simp only [cmb, comb]; subst hb'; push_cast; ring
  have e1 := starLen_comb ha hb (pts w₁).A (pts w₁).B (pts w₁).D ω₁.p1 (pts w₂).A (pts w₂).B (pts w₂).D ω₂.p1
  have e2 := starLen_comb ha hb (pts w₁).D (pts w₁).Q ((pts w₁).Q + ((2 * w₁.d + w₁.c - w₁.f : ℝ) : ℂ)) ω₁.p2
    (pts w₂).D (pts w₂).Q ((pts w₂).Q + ((2 * w₂.d + w₂.c - w₂.f : ℝ) : ℂ)) ω₂.p2
  have e3 := dist_comb ha hb (pts w₁).Q (pts w₂).Q (pts w₁).R (pts w₂).R
  push_cast at hq e2 ⊢
  rw [hq]
  simp only [comb]
  subst hb'
  nlinarith [e1, e2, e3]

theorem spVal_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (F : Fam) (w₁ w₂ : Vars) (ω₁ ω₂ : Wit) (k : SPK) :
    spVal F (comb a b w₁ w₂) (Wit.comb a b ω₁ ω₂) k ≤ a * spVal F w₁ ω₁ k + b * spVal F w₂ ω₂ k := by
  cases k with
  | zero => simp [spVal]
  | seg i j => simp only [spVal, pt_comb hab]; exact dist_comb ha hb _ _ _ _
  | star i j l => simp only [spVal, pt_comb hab, Wit.comb]; exact starLen_comb ha hb _ _ _ _ _ _ _ _
  | pair i j k l => simp only [spVal, pt_comb hab, Wit.comb]; exact pairLen_comb ha hb _ _ _ _ _ _ _ _ _ _ _ _

theorem varOf_comb (hab : a + b = 1) (F : Fam) (w₁ w₂ : Vars) (i : ℕ) :
    varOf F (comb a b w₁ w₂) i = a * varOf F w₁ i + b * varOf F w₂ i := by
  unfold varOf
  cases F
  · by_cases hi : i < 6
    · interval_cases i <;> simp [comb]
    · push_neg at hi
      have h1 : ∀ (l : List ℝ), l.length = 6 → l.getD i 0 = 0 := fun l hl => List.getD_eq_default _ _ (by omega)
      dsimp only
      rw [h1 _ (by simp), h1 _ (by simp), h1 _ (by simp)]; simp
  · by_cases hi : i < 8
    · interval_cases i <;> simp [comb]
    · push_neg at hi
      have h1 : ∀ (l : List ℝ), l.length = 8 → l.getD i 0 = 0 := fun l hl => List.getD_eq_default _ _ (by omega)
      dsimp only
      rw [h1 _ (by simp), h1 _ (by simp), h1 _ (by simp)]; simp

theorem sMinus_comb (hab : a + b = 1) (F : Fam) (sp : S43.Split) (w₁ w₂ : Vars) :
    sMinus F sp (comb a b w₁ w₂) = a * sMinus F sp w₁ + b * sMinus F sp w₂ := by
  unfold sMinus
  induction sp.sm.toList with
  | nil => simp
  | cons i t ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    split_ifs
    · have : (1 : ℝ) = a * 1 + b * 1 := by linarith
      linarith
    · rw [varOf_comb hab]; ring

theorem kVal_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (F : Fam) (L : ℕ) (w₁ w₂ : Vars) (t : TermK) :
    kVal F L (comb a b w₁ w₂) t ≤ a * kVal F L w₁ t + b * kVal F L w₂ t := by
  cases t with
  | seg i j => simp only [kVal, pt_comb hab]; exact dist_comb ha hb _ _ _ _
  | bnd K => exact bound_comb ha hb hab F L K w₁ w₂

theorem sum_kVal_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (F : Fam) (L : ℕ) (w₁ w₂ : Vars) (ks : List TermK) :
    (ks.map (kVal F L (comb a b w₁ w₂))).sum ≤ a * (ks.map (kVal F L w₁)).sum + b * (ks.map (kVal F L w₂)).sum := by
  induction ks with
  | nil => simp
  | cons t ks ih =>
    simp only [List.map_cons, List.sum_cons]
    have := kVal_comb ha hb hab F L w₁ w₂ t
    linarith

theorem gNet_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {F : Fam} {L : ℕ} {sp : S43.Split} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ks : List TermK) (sk : SPK) (w₁ w₂ : Vars) (ω₁ ω₂ : Wit) :
    gNet F L sp ρ ks sk (comb a b w₁ w₂) (Wit.comb a b ω₁ ω₂) ≤
      a * gNet F L sp ρ ks sk w₁ ω₁ + b * gNet F L sp ρ ks sk w₂ ω₂ := by
  unfold gNet
  have h1 := sum_kVal_comb ha hb hab F L w₁ w₂ ks
  have h2 := spVal_comb ha hb hab F w₁ w₂ ω₁ ω₂ sk
  have h3 := sMinus_comb hab F sp w₁ w₂
  have h4 := mul_le_mul_of_nonneg_left h1 hρ
  rw [h3]; nlinarith

/-- **the vertex set is convex** -/
theorem vset_comb (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {F : Fam} {fval L : ℕ} {sp : S43.Split} {ρ : ℝ}
    (hρ : 0 ≤ ρ) {ks : List TermK} {sk : SPK} {w₁ w₂ : Vars} {ω₁ ω₂ : Wit}
    (h₁ : vset F fval L sp ρ ks sk w₁ ω₁) (h₂ : vset F fval L sp ρ ks sk w₂ ω₂) :
    vset F fval L sp ρ ks sk (comb a b w₁ w₂) (Wit.comb a b ω₁ ω₂) := by
  obtain ⟨n₁, c₁, g₁⟩ := h₁
  obtain ⟨n₂, c₂, g₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · simp only [comb]
    exact ⟨comb_nonneg ha hb n₁.1 n₂.1, comb_nonneg ha hb n₁.2.1 n₂.2.1, comb_nonneg ha hb n₁.2.2.1 n₂.2.2.1,
      comb_nonneg ha hb n₁.2.2.2.1 n₂.2.2.2.1, comb_nonneg ha hb n₁.2.2.2.2.1 n₂.2.2.2.2.1,
      comb_nonneg ha hb n₁.2.2.2.2.2.1 n₂.2.2.2.2.2.1, comb_nonneg ha hb n₁.2.2.2.2.2.2.1 n₂.2.2.2.2.2.2.1,
      comb_nonneg ha hb n₁.2.2.2.2.2.2.2 n₂.2.2.2.2.2.2.2⟩
  · intro t ht
    have t₁ := c₁ t ht; have t₂ := c₂ t ht
    cases t with
    | seg i j => trivial
    | bnd K =>
      cases K with
      | Y =>
        intro hfv
        have := psiNet_comb ha hb hab w₁ w₂ ω₁ ω₂
        have := comb_lt ha hb hab (t₁ hfv) (t₂ hfv)
        simp at this; linarith
      | AX => exact xcond_comb ha hb hab F L .AX (by decide) w₁ w₂ ⟨n₁.2.1, n₁.2.2.2.2.2.2.1, n₁.2.2.2.2.2.2.2⟩
                ⟨n₂.2.1, n₂.2.2.2.2.2.2.1, n₂.2.2.2.2.2.2.2⟩ t₁ t₂
      | UX => exact xcond_comb ha hb hab F L .UX (by decide) w₁ w₂ ⟨n₁.2.1, n₁.2.2.2.2.2.2.1, n₁.2.2.2.2.2.2.2⟩
                ⟨n₂.2.1, n₂.2.2.2.2.2.2.1, n₂.2.2.2.2.2.2.2⟩ t₁ t₂
      | VX => exact xcond_comb ha hb hab F L .VX (by decide) w₁ w₂ ⟨n₁.2.1, n₁.2.2.2.2.2.2.1, n₁.2.2.2.2.2.2.2⟩
                ⟨n₂.2.1, n₂.2.2.2.2.2.2.1, n₂.2.2.2.2.2.2.2⟩ t₁ t₂
      | DX => exact xcond_comb ha hb hab F L .DX (by decide) w₁ w₂ ⟨n₁.2.1, n₁.2.2.2.2.2.2.1, n₁.2.2.2.2.2.2.2⟩
                ⟨n₂.2.1, n₂.2.2.2.2.2.2.1, n₂.2.2.2.2.2.2.2⟩ t₁ t₂
  · have := gNet_comb (F := F) (L := L) (sp := sp) ha hb hab hρ ks sk w₁ w₂ ω₁ ω₂
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha g₁, mul_nonpos_of_nonneg_of_nonpos hb g₂]

end S43.Stmt
