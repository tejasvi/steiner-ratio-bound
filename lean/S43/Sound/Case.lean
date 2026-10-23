import S43.Sound.Walk

/-! # One case from its skeleton and shards; the certificate theorem from the four cases -/

namespace S43

attribute [local irreducible] P

/-- what a case gives: every point of the case domain in the subcase is certified by a published split -/
def CaseOK (F : Stmt.Fam) (fval : ℕ) (ρ : ℝ) : Prop :=
  ∀ w, Stmt.domain F w → subcase fval w → ∃ sp ∈ Stmt.splits F, ∃ L ≤ 8, Stmt.certifies F sp L ρ w

theorem varOf_nonneg {F : Stmt.Fam} {w : Stmt.Vars} (hd : Stmt.domain F w) (j : ℕ) : 0 ≤ Stmt.varOf F w j := by
  obtain ⟨hb, hc, hd', hs, hu, hv, he, hf, -⟩ := hd
  cases F <;> rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [Stmt.varOf, *]

theorem case_good {F : Stmt.Fam} {fval : ℕ}
    (hcase : (F = .st ∧ (fval = 1 ∨ fval = 2)) ∨ (F = .reg ∧ (fval = 1 ∨ fval = 3))) {rho : DI} {ρ : ℝ}
    (hrho : rho.Enc ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : MonoData F fval) {skel : Codes}
    (ranges : List (ℕ × ℕ)) (hcont : contig ranges 0 (skelSize (caseOf F fval) skel) = true)
    (hshard : ∀ r ∈ ranges, ∃ cs, shardOKPar (caseOf F fval) rho skel cs r.1 r.2 = true)
    (hsome : (skelBoxes (caseOf F fval) skel).isSome = true) : CaseOK F fval ρ := by
  let G : (Fin (caseOf F fval).nb → ℝ) → Prop := fun x =>
    ∀ w, (∀ j : Fin (caseOf F fval).nb, x j = Stmt.varOf F w j) → Good F fval ρ w
  have hleaf : ∀ bx sid lid, checkRecord (caseOf F fval) rho bx sid lid ≠ .fail → ∀ x, InBox bx x → G x := by
    intro bx sid lid h x hx w hxw
    refine checkRecord_good hcase hrho hρ0 hρ1 hmono h w (fun j => ?_)
    have hj : (j : ℕ) < (caseOf F fval).nb := by rw [caseOf_nb]; exact j.isLt
    have := hx ⟨j, hj⟩
    rw [hxw ⟨j, hj⟩] at this
    exact this
  intro w hd hs
  have := case_of_shards hleaf ranges hcont hshard hsome (fun j => Stmt.varOf F w j) (fun j => varOf_nonneg hd j)
  exact this w (fun _ => rfl) hd hs

/-- the certificate theorem from the four cases -/
theorem certificate_of_cases {ρ : ℝ} (h1 : CaseOK .st 1 ρ) (h2 : CaseOK .st 2 ρ) (h3 : CaseOK .reg 1 ρ)
    (h4 : CaseOK .reg 3 ρ) (F : Stmt.Fam) (w : Stmt.Vars) (hw : Stmt.domain F w) :
    ∃ sp ∈ Stmt.splits F, ∃ L ≤ 8, Stmt.certifies F sp L ρ w := by
  by_cases hfd : w.f ≤ w.d
  · cases F
    · exact h3 w hw (by simp [subcase, hfd])
    · exact h1 w hw (by simp [subcase, hfd])
  · have hdf : w.d ≤ w.f := by linarith
    cases F
    · exact h4 w hw (by simp [subcase, hdf])
    · exact h2 w hw (by simp [subcase, hdf])

end S43
