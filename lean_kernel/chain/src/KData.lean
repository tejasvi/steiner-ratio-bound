module

public import K0Bridge
public import S43.Sound.Data

@[expose] public section

set_option maxRecDepth 100000



theorem srt_reg1 : S43.sorted4 [0, 2, 4, 5] = [0, 2, 4, 5] := List.mergeSort_of_pairwise (by decide)
theorem srt_reg2 : S43.sorted4 [1, 2, 4, 5] = [1, 2, 4, 5] := List.mergeSort_of_pairwise (by decide)
theorem srt_st1 : S43.sorted4 [0, 2, 6, 7] = [0, 2, 6, 7] := List.mergeSort_of_pairwise (by decide)
theorem srt_st2 : S43.sorted4 [1, 2, 6, 7] = [1, 2, 6, 7] := List.mergeSort_of_pairwise (by decide)

theorem mono_reg3 : S43.monoCheck .reg 3 = true := by
  unfold S43.monoCheck S43.Stmt.splits
  dsimp only
  rw [S43K.splitsReg_eq]
  simp only [S43.extOK, ← Array.contains_toList, S43.Stmt.spKind, S43.Stmt.ids, S43.idsReg, srt_reg1, srt_reg2]
  decide +kernel


theorem mono_reg1 : S43.monoCheck .reg 1 = true := by
  unfold S43.monoCheck S43.Stmt.splits
  dsimp only
  rw [S43K.splitsReg_eq]
  simp only [S43.extOK, ← Array.contains_toList, S43.Stmt.spKind, S43.Stmt.ids, S43.idsReg, srt_reg1, srt_reg2]
  decide +kernel

theorem mono_st1 : S43.monoCheck .st 1 = true := by
  unfold S43.monoCheck S43.Stmt.splits
  dsimp only
  rw [S43K.splitsSt_eq]
  simp only [S43.extOK, ← Array.contains_toList, S43.Stmt.spKind, S43.Stmt.ids, S43.idsSt, srt_st1, srt_st2]
  decide +kernel

theorem mono_st2 : S43.monoCheck .st 2 = true := by
  unfold S43.monoCheck S43.Stmt.splits
  dsimp only
  rw [S43K.splitsSt_eq]
  simp only [S43.extOK, ← Array.contains_toList, S43.Stmt.spKind, S43.Stmt.ids, S43.idsSt, srt_st1, srt_st2]
  decide +kernel

theorem size_reg : S43.sizeCheck .reg = true := by
  unfold S43.sizeCheck S43.Stmt.splits
  dsimp only
  rw [S43K.splitsReg_eq]
  decide +kernel

theorem size_st : S43.sizeCheck .st = true := by
  unfold S43.sizeCheck S43.Stmt.splits
  dsimp only
  rw [S43K.splitsSt_eq]
  decide +kernel

#print axioms mono_reg3
#print axioms mono_st1
#print axioms size_st

end
