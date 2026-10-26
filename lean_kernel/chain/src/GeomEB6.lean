module

public import GeomEB5

@[expose] public section

/-! # K1 function layer, part 6: Lemma X2's condition, Lemma Y2's Psi, the H point

Mirrors lean/'s `x2Cond_sound` (VertexSound), `psiY2PosN_sound` (EvalSound), `enc_H` (LemmaSound). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-! ## Networks at any point bound n <= 175 -/

theorem eb_star3' {n : Nat} {a b c X : PK} {za zb zc zX : ℂ} (ha : PB n a za) (hb : PB n b zb) (hc : PB n c zc)
    (hX : PB n X zX) (h1 : 50 ≤ n) (h2 : n ≤ 175) : EB 181 (star3 a b c X) (S43.Stmt.starLen za zb zc zX) := by
  unfold star3 S43.Stmt.starLen
  have d1 := eb_dist ha hX h1 h2
  have d2 := eb_dist hb hX h1 h2
  have d3 := eb_dist hc hX h1 h2
  exact eb_add (eb_add d1 d2 (by norm_num)) (d3.mono (by norm_num)) (by norm_num)

theorem eb_smt3K' {n : Nat} {a b c : PK} {za zb zc : ℂ} (ha : PB n a za) (hb : PB n b zb) (hc : PB n c zc)
    (h1 : 121 ≤ n) (h2 : n ≤ 175) :
    EB 181 (smt3K a b c) (S43.Stmt.starLen za zb zc (smt3PtK a b c za zb zc)) := by
  have dab := eb_dist ha hb (by omega) h2
  have dbc := eb_dist hb hc (by omega) h2
  have dca := eb_dist hc ha (by omega) h2
  have hX := (pb_isW (isW_fermatV a b c)).mono h1
  unfold smt3K smt3b smt3c smt3PtK
  cases hq1 : angleLe120 a b c
  · rw [Bool.cond_false]
    simp only [Bool.not_false, ite_true]
    exact ((eb_add dab dbc (by norm_num)).mono (by norm_num)).congr
      (by unfold S43.Stmt.starLen S43.Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev zc zb]; ring)
  · rw [Bool.cond_true]
    cases hq2 : angleLe120 b c a
    · rw [Bool.cond_false]
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
      exact ((eb_add dbc dca (by norm_num)).mono (by norm_num)).congr
        (by unfold S43.Stmt.starLen S43.Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev za zc]; ring)
    · rw [Bool.cond_true]
      cases hq3 : angleLe120 c a b
      · rw [Bool.cond_false]
        simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
        exact ((eb_add dca dab (by norm_num)).mono (by norm_num)).congr
          (by unfold S43.Stmt.starLen S43.Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev zb za]; ring)
      · rw [Bool.cond_true]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        exact eb_star3' ha hb hc hX (by omega) h2

/-! ## Lemma X2's condition -/

theorem x2CondK_sound {c e f : DN} {wc we wf : ℝ} (hc : EB 126 c wc) (he : EB 126 e we) (hf : EB 126 f wf)
    (h : x2Cond c e f (DN.mul TWO_OVER_SQ3_M1 c) = true) :
    we < (2 / Real.sqrt 3 - 1) * wc ∨
      (we < wc ∧ 0 < wc + we + wf - Real.sqrt (we ^ 2 + we * wf + wf ^ 2) - Real.sqrt 3 / 2 * (wc + we)) := by
  have hkc := eb_mul eb_two_over hc (by norm_num) (by norm_num)
  unfold x2Cond at h
  cases h1 : DN.ltc e (DN.mul TWO_OVER_SQ3_M1 c)
  · rw [h1, Bool.cond_false] at h
    right
    unfold x2Cond2 at h
    cases h2 : DN.ltc e c
    · rw [h2, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [h2, Bool.cond_true] at h
      refine ⟨ltcK_sound he.2 hc.2 h2, ?_⟩
      have s1 : EB 153 (DN.sq e) (we ^ 2) := eb_sq he (by norm_num) (by norm_num)
      have m1 : EB 153 (DN.mul e f) (we * wf) := eb_mul he hf (by norm_num) (by norm_num)
      have s2 : EB 153 (DN.sq f) (wf ^ 2) := eb_sq hf (by norm_num) (by norm_num)
      have a1 : EB 154 (DN.add (DN.sq e) (DN.mul e f)) (we ^ 2 + we * wf) := eb_add s1 m1 (by norm_num)
      have a2 : EB 155 (DN.add (DN.add (DN.sq e) (DN.mul e f)) (DN.sq f)) (we ^ 2 + we * wf + wf ^ 2) :=
        eb_add a1 (s2.mono (by norm_num)) (by norm_num)
      have ht := eb_sqrt a2 (by norm_num)
      have hce : EB 127 (DN.add c e) (wc + we) := eb_add hc he (by norm_num)
      have hcef : EB 128 (DN.add (DN.add c e) f) (wc + we + wf) := eb_add hce (hf.mono (by norm_num)) (by norm_num)
      have hm : EB 129 (DN.mul (DN.add c e) SQ3) ((wc + we) * Real.sqrt 3) := eb_mul hce eb_SQ3 (by norm_num) (by norm_num)
      have hhalf : EB 129 (DN.half (DN.mul (DN.add c e) SQ3)) ((wc + we) * Real.sqrt 3 / 2) := eb_half hm (by norm_num)
      have hs1 : EB 180 (DN.sub (DN.add (DN.add c e) f) (DN.sqrt (DN.add (DN.add (DN.sq e) (DN.mul e f)) (DN.sq f))))
          (wc + we + wf - Real.sqrt (we ^ 2 + we * wf + wf ^ 2)) := eb_sub (hcef.mono (by norm_num)) ht (by norm_num)
      have hphi := eb_sub hs1 (hhalf.mono (by norm_num)) (by norm_num)
      unfold x2Phi at h
      have := posK_sound hphi.2 h
      convert this using 1; ring
  · left; exact ltcK_sound he.2 hkc.2 h1

/-! ## The H point of lemma 5's U/V/D bounds -/

theorem pb_hPt {R : PK} {zR : ℂ} (hR : PB 135 R zR) {c e : DN} {wc we : ℝ} (hc : EB 126 c wc) (he : EB 126 e we) :
    PB 136 (hPt R (DN.half (DN.half (DN.sub c e)))) (zR - ((wc : ℂ) - we) / 2 * S43.Stmt.dir2) := by
  have hh : EB 127 (DN.half (DN.half (DN.sub c e))) ((wc - we) / 2 / 2) :=
    eb_half (eb_half (eb_sub hc he (by norm_num)) (by norm_num)) (by norm_num)
  have hk := eb_mul hh eb_SQ3 (by norm_num) (by norm_num)
  obtain ⟨rx, ry⟩ := R
  refine ⟨?_, ?_⟩
  · show EB 136 (DN.sub rx (DN.half (DN.half (DN.sub c e)))) _
    exact (eb_sub hR.1 (hh.mono (by norm_num)) (by norm_num)).congr
      (by simp [S43.Stmt.dir2, Complex.mul_re]; ring)
  · show EB 136 (DN.add ry (DN.mul (DN.half (DN.half (DN.sub c e))) SQ3)) _
    exact (eb_add hR.2 (hk.mono (by norm_num)) (by norm_num)).congr
      (by simp [S43.Stmt.dir2, Complex.mul_im]; ring)

end S43K

end
