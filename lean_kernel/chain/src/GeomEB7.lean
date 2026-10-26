module

public import GeomEB6
public import S43CoreK.VertexK

@[expose] public section

/-! # K1 function layer, part 7: the vertex encoding, node selection and Lemma Y2's Psi

`VEncK st W w`: the kernel vertex values enclose the case variables (box ends `< 2^126`). From it, the configuration
points of `ptsK st W` enclose `S43.Stmt.pts w` (mirror of lean/'s `ptsDI_enc` / `coords_enc`), `ptSel` selects
`S43.Stmt.pt F w i`, and an accepted `psiY2PosK` gives `0 < psiNet w ω` (mirror of `psiY2PosN_sound`). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- the family of the `st` flag -/
def famOf : Bool → S43.Stmt.Fam | true => .st | false => .reg

/-- the kernel vertex values enclose the case variables within 2^126 (u, v only for d_steiner) -/
def VEncK (st : Bool) (W : VarsK) (w : S43.Stmt.Vars) : Prop :=
  EB 126 W.b w.b ∧ EB 126 W.c w.c ∧ EB 126 W.d w.d ∧ EB 126 W.s w.s ∧ EB 126 W.e w.e ∧ EB 126 W.f w.f ∧
    (st = true → EB 126 W.u w.u ∧ EB 126 W.v w.v)

/-- the configuration points enclose `S43.Stmt.pts w` within 2^135 -/
structure PtsEncK (st : Bool) (X : PtsK) (w : S43.Stmt.Vars) : Prop where
  A : PB 135 X.A (S43.Stmt.pts w).A
  B : PB 135 X.B (S43.Stmt.pts w).B
  D : PB 135 X.D (S43.Stmt.pts w).D
  U : st = true → PB 135 X.U (S43.Stmt.pts w).U
  V : st = true → PB 135 X.V (S43.Stmt.pts w).V
  P : PB 135 X.P (S43.Stmt.pts w).P
  Q : PB 135 X.Q (S43.Stmt.pts w).Q
  R : PB 135 X.R (S43.Stmt.pts w).R
  s : PB 135 X.s (S43.Stmt.pts w).s
  r : PB 135 X.r (S43.Stmt.pts w).r

theorem PB.congr {k : Nat} {p : PK} {z z' : ℂ} (h : PB k p z) (e : z = z') : PB k p z' := e ▸ h

theorem pb_zero : PB 135 PK.zero (0 : ℂ) := by
  show EB 135 DN.zero (0 : ℂ).re ∧ EB 135 DN.zero (0 : ℂ).im
  rw [Complex.zero_re, Complex.zero_im]
  exact ⟨eb_zero.mono (by norm_num), eb_zero.mono (by norm_num)⟩

section
variable (st : Bool) (W : VarsK)
/-- (stated against a constructor application: a defeq check between a projection of `ptsK` and a point function
makes the kernel unfold the point function down to the 2^256-size literals) -/
theorem ptsK_eq : ptsK st W = ⟨PK.zero, ptB W.b, ptD W.s W.d, bif st then ptU W.s W.d W.u else PK.zero,
    bif st then ptV W.s W.d W.v else PK.zero, ptP W.s W.c, ptQ W.s W.c W.f, ptR W.s W.c W.e, S0, ptr W.s⟩ := rfl
theorem ptsK_A : (ptsK st W).A = PK.zero := by rw [ptsK_eq]
theorem ptsK_B : (ptsK st W).B = ptB W.b := by rw [ptsK_eq]
theorem ptsK_D : (ptsK st W).D = ptD W.s W.d := by rw [ptsK_eq]
theorem ptsK_U : (ptsK true W).U = ptU W.s W.d W.u := by rw [ptsK_eq, Bool.cond_true]
theorem ptsK_V : (ptsK true W).V = ptV W.s W.d W.v := by rw [ptsK_eq, Bool.cond_true, Bool.cond_true]
theorem ptsK_P : (ptsK st W).P = ptP W.s W.c := by rw [ptsK_eq]
theorem ptsK_Q : (ptsK st W).Q = ptQ W.s W.c W.f := by rw [ptsK_eq]
theorem ptsK_R : (ptsK st W).R = ptR W.s W.c W.e := by rw [ptsK_eq]
theorem ptsK_s : (ptsK st W).s = S0 := by rw [ptsK_eq]
theorem ptsK_r : (ptsK st W).r = ptr W.s := by rw [ptsK_eq]
end

theorem ptsK_enc {st : Bool} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w) : PtsEncK st (ptsK st W) w := by
  obtain ⟨hb, hc, hd, hs, he, hf, huv⟩ := hW
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ptsK_A]; exact pb_zero.congr (by simp [S43.Stmt.pts])
  · rw [ptsK_B]; exact ((pb_ptB hb).mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · rw [ptsK_D]; exact ((pb_ptD hs hd).mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · intro hst; subst hst; rw [ptsK_U]
    exact ((pb_ptU hs hd (huv rfl).1).mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · intro hst; subst hst; rw [ptsK_V]
    exact ((pb_ptV hs hd (huv rfl).2).mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · rw [ptsK_P]; exact ((pb_ptP hs hc).mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · rw [ptsK_Q]; exact (pb_ptQ hs hc hf).congr (by simp [S43.Stmt.pts])
  · rw [ptsK_R]; exact ((pb_ptR hs hc he).mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · rw [ptsK_s]; exact (pb_S0.mono (by norm_num)).congr (by simp [S43.Stmt.pts])
  · rw [ptsK_r]; exact ((pb_ptr hs).mono (by norm_num)).congr (by simp [S43.Stmt.pts])

end S43K

end
