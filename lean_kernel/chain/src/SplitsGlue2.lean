module

public import SplitsGlue

@[expose] public section

/-! # K2's split-table hypotheses `hglue`, `hsize`, `hlen` for both families -/

set_option maxRecDepth 100000

namespace S43K

theorem nSplits_false : nSplits false = 158 := rfl
theorem nSplits_true : nSplits true = 1418 := rfl

theorem hsize_of (st : Bool) : (S43.Stmt.splits (famOf st)).size = nSplits st := by
  cases st
  · show S43.splitsReg.size = 158
    rw [splitsReg_eq, List.size_toArray]; rfl
  · show S43.splitsSt.size = 1418
    rw [splitsSt_eq, List.size_toArray]; rfl

theorem hglue_of (st : Bool) :
    ∀ i, 1 ≤ i → i ≤ nSplits st → toSplit (splitK st i) = (S43.Stmt.splits (famOf st))[i - 1]! := by
  intro i h1 h2
  cases st
  · rw [nSplits_false] at h2
    have := glue_reg_aux (i - 1) (by omega)
    rw [Nat.sub_add_cancel h1] at this
    show toSplit (splitReg i) = S43.splitsReg[i - 1]!
    rw [splitsReg_eq]; exact this
  · rw [nSplits_true] at h2
    have := glue_st_aux (i - 1) (by omega)
    rw [Nat.sub_add_cancel h1] at this
    show toSplit (splitSt i) = S43.splitsSt[i - 1]!
    rw [splitsSt_eq]; exact this

theorem hlen_of (st : Bool) :
    ∀ i, 1 ≤ i → i ≤ nSplits st → (splitK st i).ta.length ≤ 40 ∧ (splitK st i).sm.length ≤ 40 := by
  intro i h1 h2
  cases st
  · rw [nSplits_false] at h2
    have := len_reg_aux (i - 1) (by omega)
    rw [Nat.sub_add_cancel h1] at this
    exact this
  · rw [nSplits_true] at h2
    have := len_st_aux (i - 1) (by omega)
    rw [Nat.sub_add_cancel h1] at this
    exact this

end S43K

#print axioms S43K.hglue_of
#print axioms S43K.hsize_of
#print axioms S43K.hlen_of

end
