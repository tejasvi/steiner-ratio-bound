module

public import S43.Sound.Bump

@[expose] public section

/-! # Unbounded sides

A record box with infinite upper ends is certified at its finite vertices only. Every point of the box is reached from its
finite face by increasing the unbounded variables one at a time, and each step keeps the network property (`vset_bump`):
the value does not increase (monotonicity rule) and the conditions survive. In the subcase `f ≥ d` with `f := d` the
coordinate `d` carries `f` with it, which is two steps (d, then f). -/

namespace S43.Stmt

/-- one step keeps the network property -/
theorem vset_bump {F : Fam} {fval L : ℕ} {sp : S43.Split} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {ks : List TermK} {sk : SPK} (i : Vr) (hLi : L = 0 ∨ i = .f) (hr : monoRule F L i sp ks sk = true)
    (hc : i = .c → .bnd .AX ∉ ks) (hY : F = .reg ∧ fval = 3 → .bnd .Y ∉ ks)
    {t : ℝ} (ht : 0 ≤ t) {w : Vars} {ω : Wit} (h : vset F fval L sp ρ ks sk w ω) :
    vset F fval L sp ρ ks sk (bump i t w) (wbump F i t sk ω) := by
  obtain ⟨hn, hcnd, hg⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hn
    cases i <;> simp only [bump] <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · intro k hk
    exact kVcond_bump i hLi ht ⟨hn.2.1, hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2⟩ ω _ k
      (fun hi he => hc hi (he ▸ hk)) (fun hfv he => hY hfv (he ▸ hk)) (hcnd k hk)
  · exact le_trans (gNet_bump_le F L i sp hρ0 hρ1 ks sk hLi hr ht w ω) hg

/-- the variable of a record coordinate -/
def vrOf (F : Fam) (j : ℕ) : Vr :=
  match F with
  | .st => [Vr.b, .c, .d, .s, .u, .v, .e, .f].getD j .b
  | .reg => [Vr.b, .c, .d, .s, .e, .f].getD j .b

/-- the conditions under which an unbounded record coordinate may be moved (what the checker requires) -/
def stepOK (F : Fam) (fval L : ℕ) (sp : S43.Split) (ks : List TermK) (sk : SPK) (j : ℕ) : Prop :=
  let i := vrOf F j
  (L = 0 ∨ i = .f) ∧ monoRule F L i sp ks sk = true ∧ (i = .c → .bnd .AX ∉ ks) ∧ (F = .reg ∧ fval = 3 → .bnd .Y ∉ ks) ∧
    (fval = 2 ∧ i = .d → monoRule F L .f sp ks sk = true)

/-- one step in a record coordinate (two bumps for `d` when `f := d`) -/
def stepMap (F : Fam) (fval : ℕ) (j : ℕ) (t : ℝ) (w : Vars) : Vars :=
  if fval = 2 ∧ vrOf F j = .d then bump .f t (bump .d t w) else bump (vrOf F j) t w

theorem embed_update (F : Fam) (fval : ℕ) (x : Fin (nbOf F fval) → ℝ) (j : Fin (nbOf F fval)) (t : ℝ) :
    embed F fval (Function.update x j (x j + t)) = stepMap F fval j.val t (embed F fval x) := by
  obtain ⟨jv, hj⟩ := j
  unfold stepMap
  cases F <;> by_cases hf : fval = 2 <;>
    (simp only [nbOf, hf, if_true, if_false] at hj
     interval_cases jv <;>
       simp [embed, bump, vrOf, Function.update, hf, Fin.ext_iff, nbOf] <;> (try split_ifs) <;> simp_all <;> ring)

theorem vset_stepMap {F : Fam} {fval L : ℕ} {sp : S43.Split} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {ks : List TermK} {sk : SPK} (j : ℕ) (hj : stepOK F fval L sp ks sk j) {t : ℝ} (ht : 0 ≤ t) {w : Vars}
    (h : ∃ ω, vset F fval L sp ρ ks sk w ω) : ∃ ω, vset F fval L sp ρ ks sk (stepMap F fval j t w) ω := by
  obtain ⟨ω, hω⟩ := h
  obtain ⟨hLi, hr, hc, hY, hf⟩ := hj
  unfold stepMap
  split_ifs with h2
  · have h1 := vset_bump hρ0 hρ1 .d (hLi.elim Or.inl (fun h => absurd (h2.2.symm.trans h) (by decide)))
      (h2.2 ▸ hr) (fun e => by cases e) hY ht hω
    exact ⟨_, vset_bump hρ0 hρ1 .f (Or.inr rfl) (hf h2) (fun e => by cases e) hY ht h1⟩
  · exact ⟨_, vset_bump hρ0 hρ1 _ hLi hr hc hY ht hω⟩

/-- **unbounded sides**: the network property on the finite face extends to the whole record box -/
theorem vset_unbounded {F : Fam} {fval L : ℕ} {sp : S43.Split} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {ks : List TermK} {sk : SPK} (lo : Fin (nbOf F fval) → ℝ) (hi : Fin (nbOf F fval) → Option ℝ)
    (hface : ∀ x, (∀ j, lo j ≤ x j ∧ x j ≤ (hi j).getD (lo j)) → ∃ ω, vset F fval L sp ρ ks sk (embed F fval x) ω)
    (hstep : ∀ j, hi j = none → stepOK F fval L sp ks sk j.val) :
    ∀ x, (∀ j, lo j ≤ x j ∧ ∀ h, hi j = some h → x j ≤ h) → ∃ ω, vset F fval L sp ρ ks sk (embed F fval x) ω := by
  intro x hx
  -- x_k: unbounded coordinates below k moved to x, the others still at lo
  let xk : ℕ → Fin (nbOf F fval) → ℝ := fun k j => if hi j = none ∧ k ≤ j.val then lo j else x j
  have h0 : ∃ ω, vset F fval L sp ρ ks sk (embed F fval (xk 0)) ω := by
    apply hface
    intro j
    simp only [xk, Nat.zero_le, and_true]
    split_ifs with hj
    · exact ⟨le_refl _, by rw [hj]; simp⟩
    · obtain ⟨h1, h2⟩ := hx j
      refine ⟨h1, ?_⟩
      obtain ⟨hv, hv'⟩ := Option.ne_none_iff_exists'.mp hj
      rw [hv']; simpa using h2 hv hv'
  have step : ∀ k, ∃ ω, vset F fval L sp ρ ks sk (embed F fval (xk k)) ω := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      by_cases hk : k < nbOf F fval
      · set j : Fin (nbOf F fval) := ⟨k, hk⟩
        by_cases hnone : hi j = none
        · -- xk (k+1) = update (xk k) j (xk k j + t), t = x j - lo j
          have hxk : xk (k + 1) = Function.update (xk k) j (xk k j + (x j - lo j)) := by
            funext i
            by_cases hij : i = j
            · subst hij; simp [xk, Function.update, hnone, j]
            · rw [Function.update_of_ne hij]
              have : i.val ≠ k := fun e => hij (Fin.ext e)
              simp only [xk]
              by_cases hn : hi i = none
              · simp only [hn, true_and]
                by_cases hle : k ≤ i.val
                · rw [if_pos (by omega), if_pos hle]
                · rw [if_neg (by omega), if_neg hle]
              · simp [hn]
          rw [hxk, embed_update]
          exact vset_stepMap hρ0 hρ1 j.val (hstep j hnone) (by linarith [(hx j).1]) ih
        · have : xk (k + 1) = xk k := by
            funext i
            simp only [xk]
            by_cases hn : hi i = none
            · have : i ≠ j := fun e => hnone (e ▸ hn)
              have : i.val ≠ k := fun e => this (Fin.ext e)
              simp only [hn, true_and]
              by_cases hle : k + 1 ≤ i.val
              · rw [if_pos hle, if_pos (by omega)]
              · rw [if_neg hle, if_neg (by omega)]
            · simp [hn]
          rw [this]; exact ih
      · have : xk (k + 1) = xk k := by
          funext i; simp only [xk]
          have := i.isLt
          by_cases hn : hi i = none
          · simp only [hn, true_and]; rw [if_neg (by omega), if_neg (by omega)]
          · simp [hn]
        rw [this]; exact ih
  have hfin : xk (nbOf F fval) = x := by
    funext i; simp only [xk]; have := i.isLt; rw [if_neg (by omega)]
  rw [← hfin]; exact step _

end S43.Stmt

end
