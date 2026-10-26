module

public import S43.Sound.Record
public import S43.Sound.Bridge

@[expose] public section

/-! # From records to points of the case domain

`Good F fval ρ w`: if `w` is in the case domain and the subcase, a published split certifies it. A record box that the
checker does not reject makes every point whose record coordinates (`proj`) lie in the box good. -/

namespace S43

attribute [local irreducible] P

/-- the subcase: `f ≤ d` (fval 1) or `d ≤ f` (fval 2: f := d, fval 3: f a box variable) -/
def subcase (fval : ℕ) (w : Stmt.Vars) : Prop := if fval = 1 then w.f ≤ w.d else w.d ≤ w.f

def Good (F : Stmt.Fam) (fval : ℕ) (ρ : ℝ) (w : Stmt.Vars) : Prop :=
  Stmt.domain F w → subcase fval w → ∃ sp ∈ Stmt.splits F, ∃ L ≤ 8, Stmt.certifies F sp L ρ w

/-- the record coordinates of a point -/
noncomputable def proj (F : Stmt.Fam) (fval : ℕ) (w : Stmt.Vars) : Fin (Stmt.nbOf F fval) → ℝ :=
  fun j => Stmt.varOf F w j

theorem embed_proj {F : Stmt.Fam} {fval : ℕ} (h2 : fval ≠ 2) (w : Stmt.Vars) (huv : F = .reg → w.u = 0 ∧ w.v = 0) :
    Stmt.embed F fval (proj F fval w) = w := by
  cases F
  · obtain ⟨hu, hv⟩ := huv rfl
    cases w; simp only at hu hv; subst hu; subst hv
    simp [Stmt.embed, proj, Stmt.nbOf, h2, Stmt.varOf]
  · simp [Stmt.embed, proj, Stmt.nbOf, h2, Stmt.varOf]

theorem embed_proj2 (w : Stmt.Vars) : Stmt.embed .st 2 (proj .st 2 w) = { w with f := w.d } := by
  simp [Stmt.embed, proj, Stmt.nbOf, Stmt.varOf]

theorem InBox.lo_le {bx : Box} {n : ℕ} {x : Fin n → ℝ} (h : InBox bx x) (j : ℕ) (hj : j < n) :
    (bx.lo[j]! : ℝ) / 2 ^ P ≤ x ⟨j, hj⟩ := (h ⟨j, hj⟩).1

theorem InBox.le_hi {bx : Box} {n : ℕ} {x : Fin n → ℝ} (h : InBox bx x) (j : ℕ) (hj : j < n) {hh : ℤ}
    (e : bx.hi[j]! = some hh) : x ⟨j, hj⟩ ≤ (hh : ℝ) / 2 ^ P := (h ⟨j, hj⟩).2 _ (by simp [hiR, e])

theorem kScond_all {F : Stmt.Fam} {fval : ℕ} {ks : List Stmt.TermK} {w : Stmt.Vars}
    (hY : ∀ k ∈ ks, k = .bnd .Y → fval = 1 ∨ (F = .reg ∧ fval = 3)) (hs : subcase fval w) :
    ∀ k ∈ ks, Stmt.kScond F fval w k := by
  intro k hk
  rcases k with ⟨a, b⟩ | K
  · trivial
  · cases K <;> try trivial
    intro hn
    rcases hY _ hk rfl with h1 | h3
    · simpa [subcase, h1] using hs
    · exact absurd h3 hn

theorem checkRecord_good {F : Stmt.Fam} {fval : ℕ}
    (hcase : (F = .st ∧ (fval = 1 ∨ fval = 2)) ∨ (F = .reg ∧ (fval = 1 ∨ fval = 3))) {rho : DI} {ρ : ℝ}
    (hrho : rho.Enc ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : MonoData F fval) {bx : Box} {sid lid : ℤ}
    (h : checkRecord (caseOf F fval) rho bx sid lid ≠ .fail) :
    ∀ w, InBox bx (proj F fval w) → Good F fval ρ w := by
  have hf2 : fval = 2 → F = .st := fun e => by rcases hcase with ⟨h1, _⟩ | ⟨_, h3 | h3⟩ <;> simp_all
  intro w hx hd hs
  have hp := pow_P_pos
  cases hv : checkRecord (caseOf F fval) rho bx sid lid
  · -- ok
    obtain ⟨sp, hsp, L, hL, ks, sk, hks, hsk, hYk, hmf, hbox⟩ := checkRecord_ok hf2 hrho hρ0 hρ1 hmono hv
    refine ⟨sp, hsp, L, hL, ?_⟩
    obtain ⟨ω, hω⟩ := hbox _ hx
    by_cases h2 : fval = 2
    · subst h2
      obtain rfl := hf2 rfl
      rw [embed_proj2] at hω
      have hdf : w.d ≤ w.f := by simpa [subcase] using hs
      have hb := Stmt.vset_bump hρ0 hρ1 (t := w.f - w.d) .f (Or.inr rfl) (hmf rfl) (fun e => by cases e)
        (fun e => by cases e.1) (by linarith) hω
      have hw : Stmt.bump .f (w.f - w.d) { w with f := w.d } = w := by
        cases w; simp only [Stmt.bump]; congr 1; ring
      rw [hw] at hb
      exact Stmt.bridge hks hsk hb (kScond_all hYk hs)
    · have huv : F = .reg → w.u = 0 ∧ w.v = 0 := fun e => by subst e; exact hd.2.2.2.2.2.2.2.2
      rw [embed_proj h2 w huv] at hω
      exact Stmt.bridge hks hsk hω (kScond_all hYk hs)
  · -- skipSym: outside max(u, v) ≤ max(b, 1)
    exfalso
    unfold checkRecord at hv
    simp only at hv
    split_ifs at hv with h1 h2
    all_goals try (simp at hv; done)
    unfold skipSym at h2
    rw [caseOf_I] at h2
    cases F
    · simp [Stmt.ids, idsReg] at h2
    · simp only [Stmt.ids, idsSt, Bool.true_and] at h2
      cases e : bx.hi[0]! with
      | none => rw [e] at h2; simp at h2
      | some hb =>
        rw [e] at h2
        have h2' : DI.imax hb ((1 <<< P : ℕ) : ℤ) < DI.imax bx.lo[4]! bx.lo[5]! := by simpa using h2
        have nb5 : 5 < Stmt.nbOf .st fval := by simp only [Stmt.nbOf]; split_ifs <;> decide
        have hb' := hx.le_hi 0 (by omega) e
        have hu' := hx.lo_le 4 (by omega)
        have hv' := hx.lo_le 5 (by omega)
        simp only [proj, Stmt.varOf, List.getD_cons_zero, List.getD_cons_succ] at hb' hu' hv'
        have hdom := hd.2.2.2.2.2.2.2.2
        simp only at hdom
        have h2r : ((DI.imax hb ((1 <<< P : ℕ) : ℤ) : ℤ) : ℝ) < ((DI.imax bx.lo[4]! bx.lo[5]! : ℤ) : ℝ) := by
          exact_mod_cast h2'
        have e2 : (((1 <<< P : ℕ) : ℤ) : ℝ) = 2 ^ P := by rw [Nat.shiftLeft_eq]; push_cast; ring
        rw [imax_cast, imax_cast, e2] at h2r
        have key : max ((hb : ℝ) / 2 ^ P) 1 < max ((bx.lo[4]! : ℝ) / 2 ^ P) ((bx.lo[5]! : ℝ) / 2 ^ P) := by
          have h2' : max (hb : ℝ) (2 ^ P) < max (bx.lo[4]! : ℝ) (bx.lo[5]! : ℝ) := h2r
          have e1 : max ((hb : ℝ) / 2 ^ P) 1 = max (hb : ℝ) (2 ^ P) / 2 ^ P := by
            rw [← max_div_div_right hp.le, div_self hp.ne']
          rw [e1, max_div_div_right hp.le]
          exact div_lt_div_of_pos_right h2' hp
        have : max w.b 1 ≤ max ((hb : ℝ) / 2 ^ P) 1 := max_le_max hb' (le_refl 1)
        have : max ((bx.lo[4]! : ℝ) / 2 ^ P) ((bx.lo[5]! : ℝ) / 2 ^ P) ≤ max w.u w.v := max_le_max hu' hv'
        linarith
  · -- skipSub: outside the subcase
    exfalso
    unfold checkRecord at hv
    simp only at hv
    split_ifs at hv with h1 h2 h3
    all_goals try (simp at hv; done)
    unfold skipSub at h3
    rw [caseOf_I, caseOf_fval] at h3
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h3
    rcases h3 with ⟨e1, h3⟩ | ⟨e3, h3⟩
    · subst e1
      cases e : bx.hi[(Stmt.ids F).vd]! with
      | none => rw [e] at h3; simp at h3
      | some hd' =>
        rw [e] at h3; replace h3 := of_decide_eq_true (by simpa using h3)
        have hvd : (Stmt.ids F).vd < Stmt.nbOf F 1 := by cases F <;> simp [Stmt.ids, idsSt, idsReg, Stmt.nbOf]
        have hvf : (Stmt.ids F).vf < Stmt.nbOf F 1 := by cases F <;> simp [Stmt.ids, idsSt, idsReg, Stmt.nbOf]
        have a1 := hx.le_hi _ hvd e
        have a2 := hx.lo_le _ hvf
        have hfd : w.f ≤ w.d := by simpa [subcase] using hs
        have : ((hd' : ℝ) / 2 ^ P) < (bx.lo[(Stmt.ids F).vf]! : ℝ) / 2 ^ P :=
          div_lt_div_of_pos_right (by exact_mod_cast h3) hp
        cases F <;> simp [proj, Stmt.varOf, Stmt.ids, idsSt, idsReg] at a1 a2 this <;> linarith
    · subst e3
      cases e : bx.hi[(Stmt.ids F).vf]! with
      | none => rw [e] at h3; simp at h3
      | some hf' =>
        rw [e] at h3; replace h3 := of_decide_eq_true (by simpa using h3)
        have hvd : (Stmt.ids F).vd < Stmt.nbOf F 3 := by cases F <;> simp [Stmt.ids, idsSt, idsReg, Stmt.nbOf]
        have hvf : (Stmt.ids F).vf < Stmt.nbOf F 3 := by cases F <;> simp [Stmt.ids, idsSt, idsReg, Stmt.nbOf]
        have a1 := hx.le_hi _ hvf e
        have a2 := hx.lo_le _ hvd
        have hdf : w.d ≤ w.f := by simpa [subcase] using hs
        have : ((hf' : ℝ) / 2 ^ P) < (bx.lo[(Stmt.ids F).vd]! : ℝ) / 2 ^ P :=
          div_lt_div_of_pos_right (by exact_mod_cast h3) hp
        cases F <;> simp [proj, Stmt.varOf, Stmt.ids, idsSt, idsReg] at a1 a2 this <;> linarith
  · exact absurd hv h

end S43

end
