module

public import GeomLem

@[expose] public section

/-! # K1: soundness of `evalVertexK` (mirror of lean/'s `evalVertexN_sound`, EvalSound.lean)

An accepted vertex gives exactly the conclusion of lean/'s `evalVertexN_sound`: the split's term kinds and S+ kind, the
Y-term side condition, and a witness `ω` with `vset`. The witness: `ω.x`, `ω.y` = the Steiner points of the S+ network
(per-vertex Fermat point, or the selected pair candidate), `ω.p1`, `ω.p2` = Psi's two star points. Built on block 2
(GeomLem) and GeomEB1-7. -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- Psi's first star point -/
noncomputable def psiP1 (st : Bool) (W : VarsK) (w : S43.Stmt.Vars) : ℂ :=
  smt3PtK (ptsK st W).A (ptsK st W).B (ptsK st W).D (S43.Stmt.pts w).A (S43.Stmt.pts w).B (S43.Stmt.pts w).D

/-- Psi's second star point -/
noncomputable def psiP2 (st : Bool) (W : VarsK) (w : S43.Stmt.Vars) : ℂ :=
  smt3PtK (ptsK st W).D (ptsK st W).Q (psiQs W.c W.d W.f (ptsK st W).Q) (S43.Stmt.pts w).D (S43.Stmt.pts w).Q
    ((S43.Stmt.pts w).Q + (2 * w.d + w.c - w.f))

/-! ## The evaluation plan with the points taken apart -/

theorem evalPlan2_eq (st : Bool) (fval L : ℕ) (W : VarsK) (ts : List TK) (sk : SK) (sm : List ℕ) :
    evalPlan2 st fval L W (ptsK st W) ts sk sm =
      evalPlan3 st fval L W (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
        (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r ts sk sm := by
  rw [ptsK_eq]; rfl

/-! ## Term kinds: membership and availability -/

theorem tKindsK_mem {st : Bool} {L : ℕ} : ∀ {ta tb : List ℕ} {ts : List TK}, tKindsK st L ta tb = some ts →
    ∀ t ∈ ts, ∃ a b, tKindK st L a b = some t
  | [], _, ts, h => by simp [tKindsK] at h; subst h; simp
  | _ :: _, [], ts, h => by simp [tKindsK] at h; subst h; simp
  | a :: as, b :: bs, ts, h => by
    simp only [tKindsK] at h
    unfold consT at h
    split at h
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at h; subst h
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨a, b, h1⟩
      · exact tKindsK_mem h2 u hu
    · exact absurd h (by simp)

theorem tKindK_bnd_avail {st : Bool} {L a b : ℕ} {K : KeyK} (h : tKindK st L a b = some (.bnd K)) :
    availK st L K = true := by
  unfold tKindK at h
  cases hc : (Nat.beq a (nXK st) || Nat.beq b (nXK st) || Nat.beq a (nYK st) || Nat.beq b (nYK st))
  · rw [hc, Bool.cond_false] at h
    cases hd : (Nat.blt a (nXK st) && Nat.blt b (nXK st))
    · rw [hd, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hd, Bool.cond_true] at h; exact absurd h (by simp)
  · rw [hc, Bool.cond_true] at h
    unfold tKindX at h
    split at h
    · exact absurd h (by simp)
    · rename_i K' _
      cases hav : availK st L K'
      · rw [hav, Bool.cond_false] at h; exact absurd h (by simp)
      · rw [hav, Bool.cond_true] at h
        simp only [Option.some.injEq, TK.bnd.injEq] at h
        subst h; exact hav

theorem tKindsK_length {st : Bool} {L : ℕ} : ∀ {ta tb : List ℕ} {ts : List TK}, tKindsK st L ta tb = some ts →
    ts.length ≤ ta.length
  | [], _, ts, h => by simp [tKindsK] at h; subst h; simp
  | _ :: _, [], ts, h => by simp [tKindsK] at h; subst h; simp
  | a :: as, b :: bs, ts, h => by
    simp only [tKindsK] at h
    unfold consT at h
    split at h
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at h; subst h
      have := tKindsK_length h2
      simp only [List.length_cons]; omega
    · exact absurd h (by simp)

/-- node ids of an S+ kind -/
def skIds : SK → List ℕ
  | .zero => []
  | .seg i j => [i, j]
  | .star i j k => [i, j, k]
  | .pair i j k l => [i, j, k, l]

theorem nXK_eq (st : Bool) : nXK st = S43.Stmt.nn (famOf st) := by cases st <;> rfl

theorem allLt_mem {n : ℕ} : ∀ {l : List ℕ}, allLt n l = true → ∀ i ∈ l, i < n
  | [], _, i, hi => by simp at hi
  | a :: l, h, i, hi => by
    simp only [allLt, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h.1
    · exact allLt_mem h.2 i hi

theorem spKind4_ids {st : Bool} {L a b c d : ℕ} {sk : SK} (h : spKind4 st L a b c d = some sk) :
    ∀ i ∈ skIds sk, i < S43.Stmt.nn (famOf st) := by
  unfold spKind4 at h
  cases st <;> simp only [Bool.cond_true, Bool.cond_false, Bool.cond_eq_ite] at h <;> split_ifs at h <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> decide

theorem spKindK_ids {st : Bool} {L : ℕ} {l : List ℕ} {sk : SK} (h : spKindK st L l = some sk) :
    ∀ i ∈ skIds sk, i < S43.Stmt.nn (famOf st) := by
  unfold spKindK at h
  cases hal : allLt (nXK st) l
  · rw [hal, Bool.cond_false] at h; exact absurd h (by simp)
  · rw [hal, Bool.cond_true] at h
    have hlt := allLt_mem hal
    rw [nXK_eq] at hlt
    match l, h with
    | [], h => simp only [spKindL, Option.some.injEq] at h; subst h; simp [skIds]
    | [_], h => simp only [spKindL, Option.some.injEq] at h; subst h; simp [skIds]
    | [a, b], h =>
      simp only [spKindL, Option.some.injEq] at h; subst h
      intro i hi; exact hlt i (by simpa [skIds] using hi)
    | [a, b, c], h =>
      simp only [spKindL, Option.some.injEq] at h; subst h
      intro i hi; exact hlt i (by simpa [skIds] using hi)
    | [a, b, c, d], h =>
      simp only [spKindL] at h
      exact spKind4_ids h
    | _ :: _ :: _ :: _ :: _ :: _, h => simp [spKindL] at h

/-! ## One T* term (mirror of `edgeValN_sound`) -/

theorem termValK_sound {st : Bool} {fval L : ℕ} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w)
    {a b : ℕ} {t : TK} (ht : tKindK st L a b = some t) {z : DN}
    (h : termValK st fval L W (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
      (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r t = some z) :
    EB 179 z (S43.Stmt.kVal (famOf st) L w (tkToN t)) ∧
      (∀ ω : S43.Stmt.Wit, ω.p1 = psiP1 st W w → ω.p2 = psiP2 st W w →
        S43.Stmt.kVcond (famOf st) fval L w ω (tkToN t)) ∧
      (tkToN t = .bnd .Y → fval = 1 ∨ (famOf st = .reg ∧ fval = 3)) := by
  have hP := ptsK_enc hW
  cases t with
  | seg i j =>
    simp only [termValK, Option.some.injEq] at h; subst h
    obtain ⟨hi, hj⟩ := tKindK_seg_lt ht
    refine ⟨?_, fun ω _ _ => trivial, fun h => by simp [tkToN] at h⟩
    simp only [tkToN, S43.Stmt.kVal]
    exact eb_dist (pb_ptSel hP hi) (pb_ptSel hP hj) (by norm_num) (by norm_num)
  | bnd K =>
    simp only [termValK] at h
    by_cases hK : K = .Y
    · subst hK
      obtain ⟨hf, cb, hcb, hz, hpsi⟩ := lemmaK_sound_Y hW hP h
      refine ⟨?_, ?_, fun _ => hf⟩
      · simp only [tkToN, keyToN, S43.Stmt.kVal, hcb, Option.elim]; exact hz
      · intro ω h1 h2
        simp only [tkToN, keyToN, S43.Stmt.kVcond]
        intro hc; exact hpsi hc ω h1 h2
    · have hav := tKindK_bnd_avail ht
      obtain ⟨-, cb, hcb, hc, hz⟩ := lemmaK_sound_X hW hP hK hav h
      refine ⟨?_, ?_, ?_⟩
      · simp only [tkToN, S43.Stmt.kVal, hcb, Option.elim]; exact hz
      · intro ω _ _
        cases K with
        | AX => simp only [tkToN, keyToN, S43.Stmt.kVcond, hcb, Option.elim] at hcb ⊢; exact hc
        | UX => simp only [tkToN, keyToN, S43.Stmt.kVcond, hcb, Option.elim] at hcb ⊢; exact hc
        | VX => simp only [tkToN, keyToN, S43.Stmt.kVcond, hcb, Option.elim] at hcb ⊢; exact hc
        | DX => simp only [tkToN, keyToN, S43.Stmt.kVcond, hcb, Option.elim] at hcb ⊢; exact hc
        | Y => exact absurd rfl hK
      · intro h'
        cases K with
        | Y => exact absurd rfl hK
        | _ => simp [tkToN, keyToN] at h'

/-! ## The T* sum (mirror of `enc_foldl_sum` with the vertex conditions) -/

theorem sumTs_sound {st : Bool} {fval L : ℕ} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w) :
    ∀ (ts : List TK), (∀ t ∈ ts, ∃ a b, tKindK st L a b = some t) →
    ∀ (acc : DN) (accR : ℝ) (k : ℕ), EB k acc accR → 179 ≤ k → k + ts.length ≤ 254 → ∀ z : DN,
      sumTs st fval L W (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
        (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r ts acc = some z →
      EB (k + ts.length) z (accR + (ts.map (fun t => S43.Stmt.kVal (famOf st) L w (tkToN t))).sum) ∧
      (∀ t ∈ ts, (∀ ω : S43.Stmt.Wit, ω.p1 = psiP1 st W w → ω.p2 = psiP2 st W w →
          S43.Stmt.kVcond (famOf st) fval L w ω (tkToN t)) ∧
        (tkToN t = .bnd .Y → fval = 1 ∨ (famOf st = .reg ∧ fval = 3)))
  | [], _, acc, accR, k, hacc, _, _, z, h => by
    simp only [sumTs, Option.some.injEq] at h; subst h
    refine ⟨?_, fun t ht => by simp at ht⟩
    simpa using hacc
  | t :: ts, hmem, acc, accR, k, hacc, hk1, hk2, z, h => by
    simp only [sumTs] at h
    split at h
    · rename_i zt hzt
      obtain ⟨a, b, hab⟩ := hmem t List.mem_cons_self
      obtain ⟨hz1, hz2, hz3⟩ := termValK_sound hW hab hzt
      have hl : k + 1 ≤ 254 := by simp only [List.length_cons] at hk2; omega
      have hacc' : EB (k + 1) (DN.add acc zt) (accR + S43.Stmt.kVal (famOf st) L w (tkToN t)) :=
        eb_add hacc (hz1.mono hk1) (by omega)
      obtain ⟨ih1, ih2⟩ := sumTs_sound hW ts (fun u hu => hmem u (List.mem_cons_of_mem _ hu)) _ _ (k + 1) hacc'
        (by omega) (by simp only [List.length_cons] at hk2; omega) z h
      refine ⟨?_, ?_⟩
      · have e : k + (t :: ts).length = k + 1 + ts.length := by simp only [List.length_cons]; omega
        rw [e]; refine ih1.congr ?_
        simp only [List.map_cons, List.sum_cons]; ring
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨hz2, hz3⟩
        · exact ih2 u hu
    · exact absurd h (by simp)

/-! ## The S+ network (mirror of `spDIN_sound`) -/

theorem spValK_sound {st : Bool} {L : ℕ} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w) {l : List ℕ}
    {sk : SK} (hsk : spKindK st L l = some sk) :
    ∃ x y : ℂ, ∀ ω : S43.Stmt.Wit, ω.x = x → ω.y = y →
      EB 183 (spValK st (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
        (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r sk) (S43.Stmt.spVal (famOf st) w ω (skToN sk)) := by
  have hP := ptsK_enc hW
  have hids := spKindK_ids hsk
  cases sk with
  | zero =>
    refine ⟨0, 0, fun ω _ _ => ?_⟩
    simp only [spValK, skToN, S43.Stmt.spVal]
    exact eb_zero.mono (by norm_num)
  | seg i j =>
    refine ⟨0, 0, fun ω _ _ => ?_⟩
    simp only [spValK, skToN, S43.Stmt.spVal]
    exact (eb_dist (pb_ptSel hP (hids i (by simp [skIds]))) (pb_ptSel hP (hids j (by simp [skIds])))
      (by norm_num) (by norm_num)).mono (by norm_num)
  | star i j k =>
    have pi := pb_ptSel hP (hids i (by simp [skIds]))
    have pj := pb_ptSel hP (hids j (by simp [skIds]))
    have pk := pb_ptSel hP (hids k (by simp [skIds]))
    refine ⟨smt3PtK
      (ptSel st i (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P (ptsK st W).Q
        (ptsK st W).R (ptsK st W).s (ptsK st W).r)
      (ptSel st j (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P (ptsK st W).Q
        (ptsK st W).R (ptsK st W).s (ptsK st W).r)
      (ptSel st k (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P (ptsK st W).Q
        (ptsK st W).R (ptsK st W).s (ptsK st W).r)
      (S43.Stmt.pt (famOf st) w i) (S43.Stmt.pt (famOf st) w j) (S43.Stmt.pt (famOf st) w k), 0, fun ω hx _ => ?_⟩
    simp only [spValK, skToN, S43.Stmt.spVal]
    rw [hx]
    exact (eb_smt3K' pi pj pk (by norm_num) (by norm_num)).mono (by norm_num)
  | pair i j k m =>
    have pi := pb_ptSel hP (hids i (by simp [skIds]))
    have pj := pb_ptSel hP (hids j (by simp [skIds]))
    have pk := pb_ptSel hP (hids k (by simp [skIds]))
    have pm := pb_ptSel hP (hids m (by simp [skIds]))
    obtain ⟨x, y, hxy⟩ := eb_pair4K pi pj pk pm
    refine ⟨x, y, fun ω hx hy => ?_⟩
    simp only [spValK, skToN, S43.Stmt.spVal]
    rw [hx, hy]; exact hxy

/-- (general: with `psiP1 ...` in place of `a`, a `rfl` here makes the elaborator unfold `psiP1` down to the DN
literals, "maximum recursion depth") -/
theorem wit_p1 (x y a b : ℂ) : (⟨x, y, a, b⟩ : S43.Stmt.Wit).p1 = a := rfl
theorem wit_p2 (x y a b : ℂ) : (⟨x, y, a, b⟩ : S43.Stmt.Wit).p2 = b := rfl

/-! ## K1 -/

theorem evalVertexK_sound {st : Bool} {fval L : ℕ} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w)
    {ρ : ℝ} (hrho : (toDI RHO).Enc ρ)
    (hn : 0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d ∧ 0 ≤ w.s ∧ 0 ≤ w.u ∧ 0 ≤ w.v ∧ 0 ≤ w.e ∧ 0 ≤ w.f) {sp : SplitK}
    (hta : sp.ta.length ≤ 40) (hsm : sp.sm.length ≤ 40) (h : evalVertexK st fval L W sp = true) :
    ∃ ks sk, S43.Stmt.tKinds (famOf st) L (toSplit sp) = some ks ∧
      S43.Stmt.spKind (famOf st) L (toSplit sp) = some sk ∧
      (∀ k ∈ ks, k = .bnd .Y → fval = 1 ∨ (famOf st = .reg ∧ fval = 3)) ∧
      ∃ ω, S43.Stmt.vset (famOf st) fval L (toSplit sp) ρ ks sk w ω := by
  unfold evalVertexK at h
  split at h
  · rename_i ts sk hts hsk
    rw [evalPlan2_eq] at h
    unfold evalPlan3 at h
    split at h
    · rename_i t ht
      have hlen := tKindsK_length hts
      obtain ⟨hT, hconds⟩ := sumTs_sound hW ts (tKindsK_mem hts) DN.zero 0 179 (eb_zero.mono (by norm_num))
        le_rfl (by omega) t ht
      obtain ⟨x, y, hS⟩ := spValK_sound hW hsk
      have hSω := hS ⟨x, y, psiP1 st W w, psiP2 st W w⟩ rfl rfl
      have hM := eb_smSum hW hsm
      have hR : EB 100 RHO ρ := ⟨RHO_bnd, hrho⟩
      have hRT := eb_mul hR hT (by omega) (by omega)
      have hRT' : EB 220 (DN.mul RHO t)
          (ρ * (0 + (ts.map (fun t => S43.Stmt.kVal (famOf st) L w (tkToN t))).sum)) := hRT.mono (by omega)
      have hA := eb_add hRT' (hSω.mono (by norm_num)) (by norm_num)
      have hD := eb_sub hA (hM.mono (by norm_num)) (by norm_num)
      unfold finV at h
      have hle := nonposK_sound hD.2 h
      refine ⟨ts.map tkToN, skToN sk, tKindsK_sound hts, spKindK_sound hsk, ?_,
        ⟨x, y, psiP1 st W w, psiP2 st W w⟩, hn, ?_, ?_⟩
      · intro k hk hkY
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hk
        exact (hconds u hu).2 hkY
      · intro k hk
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hk
        exact (hconds u hu).1 _ (wit_p1 x y _ _) (wit_p2 x y _ _)
      · unfold S43.Stmt.gNet
        rw [List.map_map]
        have e : (ts.map ((S43.Stmt.kVal (famOf st) L w) ∘ tkToN)) =
            ts.map (fun t => S43.Stmt.kVal (famOf st) L w (tkToN t)) := rfl
        rw [e]
        simpa using hle
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end S43K

end
