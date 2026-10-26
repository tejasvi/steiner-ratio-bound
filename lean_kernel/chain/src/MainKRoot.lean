module

public import MainKTemplate

@[expose] public section

/-! # K4 at the root stacks

`steiner_ratio_geK` with every case's root stack the one box `[0, ∞)^nb` (where the unit stream starts), so the
coverage hypotheses `hr1`-`hr4` are discharged by `root_cover`. What is left are the four `Transfer` facts, one per case:
the aggregators' top theorems (`transfer_trans` over the units' `unit_transfer`). The final file states
`certificate` and `steiner_ratio_ge` with no hypotheses and checks them against the statements by `example`s, as
lean/'s S43Final.lean does. -/

namespace S43K

/-- the root stack of a case: the one box `[0, ∞)^nb` -/
def rootStack (nb : ℕ) : List BoxS := [⟨List.replicate nb 0, List.replicate nb none⟩]

theorem rootStack_cover (n : ℕ) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) : ∃ b ∈ rootStack n, InBoxS b x :=
  ⟨_, List.mem_singleton_self _, root_cover n x hx⟩

theorem certificateK_root
    (hT1 : Transfer true 1 (S43.Stmt.nbOf .st 1) (rootStack (S43.Stmt.nbOf .st 1)) [])
    (hT2 : Transfer true 2 (S43.Stmt.nbOf .st 2) (rootStack (S43.Stmt.nbOf .st 2)) [])
    (hT3 : Transfer false 1 (S43.Stmt.nbOf .reg 1) (rootStack (S43.Stmt.nbOf .reg 1)) [])
    (hT4 : Transfer false 3 (S43.Stmt.nbOf .reg 3) (rootStack (S43.Stmt.nbOf .reg 3)) [])
    (F : S43.Stmt.Fam) (w : S43.Stmt.Vars) (hw : S43.Stmt.domain F w) :
    ∃ sp ∈ S43.Stmt.splits F, ∃ L ≤ 8, S43.Stmt.certifies F sp L (2141 / 2500) w :=
  certificateK (rootStack_cover _) (rootStack_cover _) (rootStack_cover _) (rootStack_cover _) hT1 hT2 hT3 hT4 F w hw

theorem steiner_ratio_geK_root
    (hT1 : Transfer true 1 (S43.Stmt.nbOf .st 1) (rootStack (S43.Stmt.nbOf .st 1)) [])
    (hT2 : Transfer true 2 (S43.Stmt.nbOf .st 2) (rootStack (S43.Stmt.nbOf .st 2)) [])
    (hT3 : Transfer false 1 (S43.Stmt.nbOf .reg 1) (rootStack (S43.Stmt.nbOf .reg 1)) [])
    (hT4 : Transfer false 3 (S43.Stmt.nbOf .reg 3) (rootStack (S43.Stmt.nbOf .reg 3)) [])
    (Real : S43.Stmt.Realized) (H : S43.Stmt.LemmaLayer Real) :
    ∀ P : Finset ℂ, (2141 / 2500 : ℝ) * S43.Stmt.mstLength P ≤ S43.Stmt.steinerLength P :=
  steiner_ratio_geK (rootStack_cover _) (rootStack_cover _) (rootStack_cover _) (rootStack_cover _)
    hT1 hT2 hT3 hT4 Real H

end S43K

#print axioms S43K.certificateK_root
#print axioms S43K.steiner_ratio_geK_root

end
