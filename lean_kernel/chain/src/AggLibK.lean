module

public import MainKRoot
public import S43KChainU

@[expose] public section

/-! # The final theorems from the four case roots

The aggregators chain each case's units into `ChainK k (rootStackK k) []` (S43KChainU, which imports only the walk
library). Here `ChainU` becomes K3's `Transfer` (`transfer_of_chainU`, by induction from `unit_transfer` and
`transfer_trans`), and the four roots give `MainKRoot`'s four hypotheses. The chain predicate lives in S43KChainU so that
the aggregators need neither Mathlib nor lean/'s files. -/

namespace S43K

theorem transfer_of_chainU {st : Bool} {fval nb : ℕ} {S T : List BoxS} (h : ChainU st fval nb S T) :
    Transfer st fval nb S T := by
  induction h with
  | unit h => exact unit_transfer h
  | trans _ _ ih1 ih2 => exact transfer_trans ih1 ih2

theorem hT_of_root1 (h : ChainK 1 (rootStackK 1) []) :
    Transfer false 3 (S43.Stmt.nbOf .reg 3) (rootStack (S43.Stmt.nbOf .reg 3)) [] := transfer_of_chainU h
theorem hT_of_root2 (h : ChainK 2 (rootStackK 2) []) :
    Transfer true 2 (S43.Stmt.nbOf .st 2) (rootStack (S43.Stmt.nbOf .st 2)) [] := transfer_of_chainU h
theorem hT_of_root3 (h : ChainK 3 (rootStackK 3) []) :
    Transfer false 1 (S43.Stmt.nbOf .reg 1) (rootStack (S43.Stmt.nbOf .reg 1)) [] := transfer_of_chainU h
theorem hT_of_root4 (h : ChainK 4 (rootStackK 4) []) :
    Transfer true 1 (S43.Stmt.nbOf .st 1) (rootStack (S43.Stmt.nbOf .st 1)) [] := transfer_of_chainU h

/-- the final theorem from the four roots -/
theorem steiner_ratio_geK_roots (h1 : ChainK 1 (rootStackK 1) []) (h2 : ChainK 2 (rootStackK 2) [])
    (h3 : ChainK 3 (rootStackK 3) []) (h4 : ChainK 4 (rootStackK 4) [])
    (Real : S43.Stmt.Realized) (H : S43.Stmt.LemmaLayer Real) :
    ∀ P : Finset ℂ, (2141 / 2500 : ℝ) * S43.Stmt.mstLength P ≤ S43.Stmt.steinerLength P :=
  steiner_ratio_geK_root (hT_of_root4 h4) (hT_of_root2 h2) (hT_of_root3 h3) (hT_of_root1 h1) Real H

theorem certificateK_roots (h1 : ChainK 1 (rootStackK 1) []) (h2 : ChainK 2 (rootStackK 2) [])
    (h3 : ChainK 3 (rootStackK 3) []) (h4 : ChainK 4 (rootStackK 4) [])
    (F : S43.Stmt.Fam) (w : S43.Stmt.Vars) (hw : S43.Stmt.domain F w) :
    ∃ sp ∈ S43.Stmt.splits F, ∃ L ≤ 8, S43.Stmt.certifies F sp L (2141 / 2500) w :=
  certificateK_root (hT_of_root4 h4) (hT_of_root2 h2) (hT_of_root3 h3) (hT_of_root1 h1) F w hw

end S43K

/-! shape checks: unit claims with literal case data feed `chainK_of_unit` by unfolding -/
example (S : List S43K.BoxS) (u1 : S43K.UnitClaim false 3 6 (S43K.rootStackK 1) S) (u2 : S43K.UnitClaim false 3 6 S []) :
    S43K.ChainK 1 (S43K.rootStackK 1) [] := S43K.chainK_trans (S43K.chainK_of_unit u1) (S43K.chainK_of_unit u2)
example (S : List S43K.BoxS) (u : S43K.UnitClaim true 1 8 S []) : S43K.ChainK 4 S [] := S43K.chainK_of_unit u
example (S : List S43K.BoxS) (u : S43K.UnitClaim true 2 7 S []) : S43K.ChainK 2 S [] := S43K.chainK_of_unit u
example (S : List S43K.BoxS) (u : S43K.UnitClaim false 1 6 S []) : S43K.ChainK 3 S [] := S43K.chainK_of_unit u
example : S43K.rootStackK 4 = [⟨[0, 0, 0, 0, 0, 0, 0, 0], [none, none, none, none, none, none, none, none]⟩] := rfl
example : S43K.rootStackK 2 = [⟨[0, 0, 0, 0, 0, 0, 0], [none, none, none, none, none, none, none]⟩] := rfl
example : S43K.rootStackK 1 = [⟨[0, 0, 0, 0, 0, 0], [none, none, none, none, none, none]⟩] := rfl

end
