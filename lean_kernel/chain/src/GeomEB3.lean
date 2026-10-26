module

public import GeomEB2

@[expose] public section

/-! # K1 function layer, part 3: the configuration points

Mirror of lean/'s `ptsDI_enc`: from `EB 126` enclosures of the vertex values (box ends `< 2^126`, the `allBelow` check of
`checkRecordK`), every configuration point of `ptsK` is a `PB 135` enclosure of the corresponding point of
`S43.Stmt.pts w`. -/

set_option maxRecDepth 100000

namespace S43K
open DN

section
variable {b c d s u v e f : DN} {wb wc wd ws wu wv we wf : ℝ}

theorem pb_ptr (hs : EB 126 s ws) : PB 129 (ptr s) (1 + (ws : ℂ) * S43.Stmt.dir2) := by
  have := pb_addDir (pb_S0.mono (by norm_num)) hs (by norm_num) (by norm_num) false false
  simp at this; exact this

theorem pb_ptP (hs : EB 126 s ws) (hc : EB 126 c wc) :
    PB 132 (ptP s c) (1 + (ws : ℂ) * S43.Stmt.dir2 - (wc : ℂ) * S43.Stmt.dir1) := by
  have := pb_addDir (pb_ptr hs) (hc.mono (by norm_num)) (by norm_num) (by norm_num) true true
  simp only [ite_true, Complex.ofReal_neg, neg_mul] at this
  rwa [← sub_eq_add_neg] at this

theorem pb_ptD (hs : EB 126 s ws) (hd : EB 126 d wd) :
    PB 130 (ptD s d) (1 + (ws : ℂ) * S43.Stmt.dir2 + (wd : ℂ) * S43.Stmt.dir0) := by
  have hr := pb_ptr hs
  refine ⟨?_, ?_⟩
  · show EB 130 (DN.add (ptr s).x d) _
    exact (eb_add hr.1 (hd.mono (by norm_num)) (by norm_num)).congr (by simp [S43.Stmt.dir0])
  · show EB 130 (ptr s).y _
    exact (hr.2.mono (by norm_num)).congr (by simp [S43.Stmt.dir0])

theorem pb_ptB (hb : EB 126 b wb) : PB 129 (ptB b) (1 + (wb : ℂ) * S43.Stmt.dir1) := by
  have := pb_addDir (pb_S0.mono (by norm_num)) hb (by norm_num) (by norm_num) true false
  simp at this; exact this

theorem pb_ptU (hs : EB 126 s ws) (hd : EB 126 d wd) (hu : EB 126 u wu) :
    PB 133 (ptU s d u) (1 + (ws : ℂ) * S43.Stmt.dir2 + (wd : ℂ) * S43.Stmt.dir0 + (wu : ℂ) * S43.Stmt.dir1) := by
  have := pb_addDir (pb_ptD hs hd) (hu.mono (by norm_num)) (by norm_num) (by norm_num) true false
  simp at this; exact this

theorem pb_ptV (hs : EB 126 s ws) (hd : EB 126 d wd) (hv : EB 126 v wv) :
    PB 133 (ptV s d v) (1 + (ws : ℂ) * S43.Stmt.dir2 + (wd : ℂ) * S43.Stmt.dir0 + (wv : ℂ) * S43.Stmt.dir2) := by
  have := pb_addDir (pb_ptD hs hd) (hv.mono (by norm_num)) (by norm_num) (by norm_num) false false
  simp at this; exact this

theorem pb_ptQ (hs : EB 126 s ws) (hc : EB 126 c wc) (hf : EB 126 f wf) :
    PB 135 (ptQ s c f)
      (1 + (ws : ℂ) * S43.Stmt.dir2 - (wc : ℂ) * S43.Stmt.dir1 + (wf : ℂ) * S43.Stmt.dir2) := by
  have := pb_addDir (pb_ptP hs hc) (hf.mono (by norm_num)) (by norm_num) (by norm_num) false false
  simp at this; exact this

theorem pb_ptR (hs : EB 126 s ws) (hc : EB 126 c wc) (he : EB 126 e we) :
    PB 133 (ptR s c e) (1 + (ws : ℂ) * S43.Stmt.dir2 - (wc : ℂ) * S43.Stmt.dir1 - (we : ℂ) * S43.Stmt.dir0) := by
  have hP := pb_ptP hs hc
  refine ⟨?_, ?_⟩
  · show EB 133 (DN.sub (ptP s c).x e) _
    exact (eb_sub hP.1 (he.mono (by norm_num)) (by norm_num)).congr (by simp [S43.Stmt.dir0])
  · show EB 133 (ptP s c).y _
    exact (hP.2.mono (by norm_num)).congr (by simp [S43.Stmt.dir0])

end

end S43K

end
