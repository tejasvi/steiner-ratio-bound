module

public import K0Bridge
public import GeomLem
public import S43CoreK.CheckK

@[expose] public section

/-! # The kernel split table equals the statement's split lists

`splitSt i` / `splitReg i` (SplitsK, a binary-search tree, 1-based) are the K0 literals `splitsLit*L`, hence
(K0, `splitsSt_eq`) the statement's `S43.splitsSt` / `splitsReg`. Kernel-decided; these discharge K2's `hglue`, `hsize`,
`hlen`. -/

set_option maxRecDepth 100000

namespace S43K

theorem glue_st_aux : ∀ i < 1418, toSplit (splitSt (i + 1)) = splitsLitStL.toArray[i]! := by decide +kernel
theorem glue_reg_aux : ∀ i < 158, toSplit (splitReg (i + 1)) = splitsLitRegL.toArray[i]! := by decide +kernel
theorem len_st_aux : ∀ i < 1418, (splitSt (i + 1)).ta.length ≤ 40 ∧ (splitSt (i + 1)).sm.length ≤ 40 := by
  decide +kernel
theorem len_reg_aux : ∀ i < 158, (splitReg (i + 1)).ta.length ≤ 40 ∧ (splitReg (i + 1)).sm.length ≤ 40 := by
  decide +kernel

end S43K

end
