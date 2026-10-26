module

public import WalkSoundK
public import SplitsGlue2
public import KData
public import S43.Sound.MainProof

@[expose] public section

/-! # The main theorem from the four case walks

The final assembly of lean/ (S43Final.lean) with its case facts replaced by kernel ones:
`certificate_of_cases` and `main_of_certificate` (from lean/, unchanged), the case theorems `case_goodK`
(K3/K4) and the data facts `monoCheck` /
`sizeCheck` decided in the kernel (KData). The case walks enter as `Transfer` facts from the root stacks to the empty
stack (in the final assembly: the aggregator theorems over the unit claims), with their root coverage. -/

set_option maxRecDepth 100000

namespace S43K

theorem rho_enc : (toDI RHO).Enc (2141 / 2500 : ℝ) := by
  have h := eb_RHO.2
  convert h using 1

theorem caseOK_of_transfer (st : Bool) (fval : ℕ)
    (hcase : (st = true ∧ (fval = 1 ∨ fval = 2)) ∨ (st = false ∧ (fval = 1 ∨ fval = 3)))
    (hmono : S43.MonoData (famOf st) fval) {rootSk : List BoxS}
    (hroot : ∀ x : Fin (S43.Stmt.nbOf (famOf st) fval) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ rootSk, InBoxS b x)
    (hT : Transfer st fval (S43.Stmt.nbOf (famOf st) fval) rootSk []) :
    S43.CaseOK (famOf st) fval (2141 / 2500) :=
  case_goodK hcase rho_enc (by norm_num) (by norm_num) hmono (hglue_of st) (hsize_of st) (hlen_of st) hroot hT

theorem certificateK {r1 r2 r3 r4 : List BoxS}
    (hr1 : ∀ x : Fin (S43.Stmt.nbOf .st 1) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r1, InBoxS b x)
    (hr2 : ∀ x : Fin (S43.Stmt.nbOf .st 2) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r2, InBoxS b x)
    (hr3 : ∀ x : Fin (S43.Stmt.nbOf .reg 1) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r3, InBoxS b x)
    (hr4 : ∀ x : Fin (S43.Stmt.nbOf .reg 3) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r4, InBoxS b x)
    (hT1 : Transfer true 1 (S43.Stmt.nbOf .st 1) r1 []) (hT2 : Transfer true 2 (S43.Stmt.nbOf .st 2) r2 [])
    (hT3 : Transfer false 1 (S43.Stmt.nbOf .reg 1) r3 []) (hT4 : Transfer false 3 (S43.Stmt.nbOf .reg 3) r4 [])
    (F : S43.Stmt.Fam) (w : S43.Stmt.Vars) (hw : S43.Stmt.domain F w) :
    ∃ sp ∈ S43.Stmt.splits F, ∃ L ≤ 8, S43.Stmt.certifies F sp L (2141 / 2500) w :=
  S43.certificate_of_cases
    (caseOK_of_transfer true 1 (Or.inl ⟨rfl, Or.inl rfl⟩) (S43.monoData_of_check mono_st1) hr1 hT1)
    (caseOK_of_transfer true 2 (Or.inl ⟨rfl, Or.inr rfl⟩) (S43.monoData_of_check mono_st2) hr2 hT2)
    (caseOK_of_transfer false 1 (Or.inr ⟨rfl, Or.inl rfl⟩) (S43.monoData_of_check mono_reg1) hr3 hT3)
    (caseOK_of_transfer false 3 (Or.inr ⟨rfl, Or.inr rfl⟩) (S43.monoData_of_check mono_reg3) hr4 hT4)
    F w hw

theorem steiner_ratio_geK {r1 r2 r3 r4 : List BoxS}
    (hr1 : ∀ x : Fin (S43.Stmt.nbOf .st 1) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r1, InBoxS b x)
    (hr2 : ∀ x : Fin (S43.Stmt.nbOf .st 2) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r2, InBoxS b x)
    (hr3 : ∀ x : Fin (S43.Stmt.nbOf .reg 1) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r3, InBoxS b x)
    (hr4 : ∀ x : Fin (S43.Stmt.nbOf .reg 3) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ r4, InBoxS b x)
    (hT1 : Transfer true 1 (S43.Stmt.nbOf .st 1) r1 []) (hT2 : Transfer true 2 (S43.Stmt.nbOf .st 2) r2 [])
    (hT3 : Transfer false 1 (S43.Stmt.nbOf .reg 1) r3 []) (hT4 : Transfer false 3 (S43.Stmt.nbOf .reg 3) r4 [])
    (Real : S43.Stmt.Realized) (H : S43.Stmt.LemmaLayer Real) :
    ∀ P : Finset ℂ, (2141 / 2500 : ℝ) * S43.Stmt.mstLength P ≤ S43.Stmt.steinerLength P :=
  S43.Stmt.main_of_certificate (by norm_num)
    (fun F => by cases F; exacts [S43.size_of_check size_reg, S43.size_of_check size_st])
    (certificateK hr1 hr2 hr3 hr4 hT1 hT2 hT3 hT4) Real H.trap H.domain H.duHwang

end S43K

#print axioms S43K.steiner_ratio_geK
example : True := trivial

end
