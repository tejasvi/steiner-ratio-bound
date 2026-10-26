module

public import GeomEB7

@[expose] public section

/-! # K1, block 2: Lemma Y2's Psi, the lemma entries, the term/S+ kinds, node selection and the S- sum

Context (all in GeomEB*.lean, building on OpLayer):
* `EB k a x` = `BndD k a ∧ (toDI a).Enc x`; `PB k p z` = both coordinates `EB k`; op lemmas `eb_add`, `eb_sub`, `eb_mul`,
  `eb_half`, `eb_max`, `eb_nmul2/3`, `eb_divSQ3`, constants `eb_one`, `eb_two_over`, `eb_SQ3`; comparisons
  `ltcK_sound`, `lecK_sound`, `gecK_sound`, `posK_sound`.
* `VEncK st W w`: vertex values within 2^126; `PtsEncK st (ptsK st W) w` (from `ptsK_enc`): points within 2^135.
* networks: `eb_dist` (EB 179), `eb_smt3K'` (EB 181, any point bound n in [121, 175]), `eb_maxd2/3/4` (EB 179),
  `x2CondK_sound`, `pb_hPt`, `smt3PtK`.
* Exponents at M = 126 (static bounds). Counterparts in lean/: S43/Sound/LemmaSound.lean (`lemmaEntry_sound`),
  EvalSound.lean (`psiY2PosN_sound`, `edgeValN_sound`), Net.lean (`tKind`, `spKind`), Statements.lean (`lemmaBound`).
Proof-engineering notes: no `simp only [def]` on definitions holding the 2^256-size
literals (`unfold`); no rfl/defeq between a projection or `cond` and a point/DN function (use the constructor-form
equation `ptsK_eq`, the field lemmas `ptsK_*`, and `rw [Bool.cond_true]` per occurrence); `generalize` big powers before
linarith; explicit exponent ascriptions (`have h : EB 153 ... := ...`) before combining `eb_sq`/`eb_mul` results. -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-! ## Fixed definitions -/

def keyToN : KeyK → S43.Stmt.Key
  | .AX => .AX | .UX => .UX | .VX => .VX | .DX => .DX | .Y => .Y

def tkToN : TK → S43.Stmt.TermK
  | .seg i j => .seg i j
  | .bnd K => .bnd (keyToN K)

def skToN : SK → S43.Stmt.SPK
  | .zero => .zero
  | .seg i j => .seg i j
  | .star i j k => .star i j k
  | .pair i j k l => .pair i j k l

/-- the split of lean/ (`S43.Split`) of a kernel split -/
def toSplit (sp : SplitK) : S43.Split := ⟨sp.sm.toArray, sp.sp.toArray, sp.ta.toArray, sp.tb.toArray, sp.mono⟩

/-! ## Helper lemmas for the proofs below -/

/-- node selection from any points that enclose the configuration -/
theorem pb_ptSel_gen {st : Bool} {w : S43.Stmt.Vars} {X : PtsK} (hP : PtsEncK st X w) {i : ℕ}
    (hi : i < S43.Stmt.nn (famOf st)) :
    PB 135 (ptSel st i X.A X.B X.D X.U X.V X.P X.Q X.R X.s X.r) (S43.Stmt.pt (famOf st) w i) := by
  cases st
  · have hi' : i < 8 := hi
    interval_cases i
    · exact hP.A
    · exact hP.B
    · exact hP.D
    · exact hP.P
    · exact hP.Q
    · exact hP.R
    · exact hP.s
    · exact hP.r
  · have hi' : i < 10 := hi
    interval_cases i
    · exact hP.A
    · exact hP.B
    · exact hP.D
    · exact hP.U rfl
    · exact hP.V rfl
    · exact hP.P
    · exact hP.Q
    · exact hP.R
    · exact hP.s
    · exact hP.r

theorem nble_false {x y : Nat} (h : y < x) : Nat.ble x y = false := by
  apply Bool.eq_false_iff.mpr; intro h'; have := ble_true h'; omega

theorem nbeq_false {x y : Nat} (h : x ≠ y) : Nat.beq x y = false := by
  apply Bool.eq_false_iff.mpr; intro h'; exact h (Nat.eq_of_beq_eq_true h')

/-- the vertex value of variable `j` encloses the statement's `varOf` -/
theorem eb_varK {st : Bool} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w) (j : ℕ) :
    EB 126 (varK st W j) (S43.Stmt.varOf (famOf st) w j) := by
  obtain ⟨hb, hc, hd, hs, he, hf, huv⟩ := hW
  have hz : EB 126 DN.zero 0 := eb_zero.mono (by norm_num)
  cases st
  · rcases (show j < 6 ∨ 6 ≤ j by omega) with hj | hj
    · interval_cases j
      · exact hb
      · exact hc
      · exact hd
      · exact hs
      · exact he
      · exact hf
    · unfold varK
      simp only [nble_false (show 3 < j by omega), nbeq_false (show j ≠ 4 by omega),
        nbeq_false (show j ≠ 5 by omega), Bool.cond_false]
      have e : S43.Stmt.varOf (famOf false) w j = 0 := by
        show [w.b, w.c, w.d, w.s, w.e, w.f].getD j 0 = 0
        exact List.getD_eq_default _ _ (by simp; omega)
      rw [e]; exact hz
  · obtain ⟨hu, hv⟩ := huv rfl
    rcases (show j < 8 ∨ 8 ≤ j by omega) with hj | hj
    · interval_cases j
      · exact hb
      · exact hc
      · exact hd
      · exact hs
      · exact hu
      · exact hv
      · exact he
      · exact hf
    · unfold varK
      simp only [nble_false (show 3 < j by omega), nbeq_false (show j ≠ 4 by omega),
        nbeq_false (show j ≠ 5 by omega), nbeq_false (show j ≠ 6 by omega),
        nbeq_false (show j ≠ 7 by omega), Bool.cond_false, Bool.cond_true]
      have e : S43.Stmt.varOf (famOf true) w j = 0 := by
        show [w.b, w.c, w.d, w.s, w.u, w.v, w.e, w.f].getD j 0 = 0
        exact List.getD_eq_default _ _ (by simp; omega)
      rw [e]; exact hz

/-- one step of `smSum` (the kernel must not compare two `smSum` applications with different accumulators: its
argument check compares the accumulators first and unfolds `DN.add` down to `Nat.sub _ B`; so both sides are reduced to
the same internal term instead) -/
theorem smSum_cons (st : Bool) (W : VarsK) (e : Nat) (es : List Nat) (acc : DN) :
    smSum st W (e :: es) acc =
      smSum st W es (DN.add acc (bif Nat.beq e 0 then DN.one else varK st W (Nat.sub e 1))) := by
  conv_lhs => delta smSum; whnf
  conv_rhs => delta smSum; whnf

theorem smSum_nil (st : Bool) (W : VarsK) (acc : DN) : smSum st W [] acc = acc := by
  conv_lhs => delta smSum; whnf

theorem eb_smSum_aux {st : Bool} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w) (l : List ℕ) :
    ∀ (k : ℕ) (acc : DN) (a : ℝ), 126 ≤ k → k + l.length ≤ 254 → EB k acc a →
      EB (k + l.length) (smSum st W l acc)
        (a + (l.map fun i => if i = 0 then (1 : ℝ) else S43.Stmt.varOf (famOf st) w (i - 1)).sum) := by
  induction l with
  | nil =>
    intro k acc a _ _ h
    rw [smSum_nil]
    simp only [List.length_nil, List.map_nil, List.sum_nil, add_zero]
    exact h
  | cons e es ih =>
    intro k acc a hk hl h
    simp only [List.length_cons] at hl
    have ht : EB k (bif Nat.beq e 0 then DN.one else varK st W (Nat.sub e 1))
        (if e = 0 then (1 : ℝ) else S43.Stmt.varOf (famOf st) w (e - 1)) := by
      by_cases he0 : e = 0
      · subst he0
        rw [show Nat.beq 0 0 = true from rfl, Bool.cond_true, ite_eq_left rfl]
        exact eb_one.mono (by omega)
      · rw [nbeq_false he0, Bool.cond_false, ite_eq_right he0]
        exact (eb_varK hW (e - 1)).mono hk
    have ih' := ih (k + 1) (DN.add acc (bif Nat.beq e 0 then DN.one else varK st W (Nat.sub e 1)))
      (a + (if e = 0 then (1 : ℝ) else S43.Stmt.varOf (famOf st) w (e - 1))) (by omega) (by omega)
      (eb_add h ht (by omega))
    rw [show k + (e :: es).length = k + 1 + es.length by simp; omega, smSum_cons]
    refine ih'.congr ?_
    simp only [List.map_cons, List.sum_cons]; ring

theorem psiQs_eq (c d f qx qy : DN) :
    psiQs c d f ⟨qx, qy⟩ = ⟨DN.add qx (DN.sub (DN.add (DN.nmul2 d) c) f), qy⟩ := rfl

/-- `psiY2PosK` at any points and values that enclose the configuration -/
theorem psiY2PosK_gen {b c d s e f : DN} {A Bp D Q R : PK} {w : S43.Stmt.Vars}
    (hb : EB 126 b w.b) (hc : EB 126 c w.c) (hd : EB 126 d w.d) (hs : EB 126 s w.s) (he : EB 126 e w.e)
    (hf : EB 126 f w.f) (hA : PB 135 A (S43.Stmt.pts w).A) (hB : PB 135 Bp (S43.Stmt.pts w).B)
    (hD : PB 135 D (S43.Stmt.pts w).D) (hQ : PB 135 Q (S43.Stmt.pts w).Q) (hR : PB 135 R (S43.Stmt.pts w).R)
    (h : psiY2PosK b c d s e f A Bp D Q R = true) {ω : S43.Stmt.Wit}
    (h1 : ω.p1 = smt3PtK A Bp D (S43.Stmt.pts w).A (S43.Stmt.pts w).B (S43.Stmt.pts w).D)
    (h2 : ω.p2 = smt3PtK D Q (psiQs c d f Q) (S43.Stmt.pts w).D (S43.Stmt.pts w).Q
      ((S43.Stmt.pts w).Q + (2 * w.d + w.c - w.f))) :
    0 < S43.Stmt.psiNet w ω := by
  have e1 : EB 127 (DN.add DN.one b) (1 + w.b) := eb_add (eb_one.mono (by norm_num)) hb (by norm_num)
  have e2 : EB 128 (DN.add (DN.add DN.one b) s) (1 + w.b + w.s) := eb_add e1 (hs.mono (by norm_num)) (by norm_num)
  have e3 : EB 128 (DN.nmul3 d) (3 * w.d) := eb_nmul3 hd (by norm_num)
  have e4 : EB 129 (DN.add (DN.add (DN.add DN.one b) s) (DN.nmul3 d)) (1 + w.b + w.s + 3 * w.d) :=
    eb_add e2 e3 (by norm_num)
  have e5 : EB 127 (DN.nmul2 c) (2 * w.c) := eb_nmul2 hc (by norm_num)
  have e6 : EB 130 (DN.add (DN.add (DN.add (DN.add DN.one b) s) (DN.nmul3 d)) (DN.nmul2 c))
      (1 + w.b + w.s + 3 * w.d + 2 * w.c) := eb_add e4 (e5.mono (by norm_num)) (by norm_num)
  have e7 : EB 131 (psi0 b c d s e) (1 + w.b + w.s + 3 * w.d + 2 * w.c + w.e) :=
    eb_add e6 (he.mono (by norm_num)) (by norm_num)
  have s1 := eb_smt3K' hA hB hD (by norm_num) (by norm_num)
  obtain ⟨qx, qy⟩ := Q
  have hQs : PB 136 (psiQs c d f ⟨qx, qy⟩) ((S43.Stmt.pts w).Q + (2 * w.d + w.c - w.f)) := by
    rw [psiQs_eq]
    have t1 : EB 128 (DN.add (DN.nmul2 d) c) (2 * w.d + w.c) :=
      eb_add (eb_nmul2 hd (by norm_num)) (hc.mono (by norm_num)) (by norm_num)
    have t2 : EB 129 (DN.sub (DN.add (DN.nmul2 d) c) f) (2 * w.d + w.c - w.f) :=
      eb_sub t1 (hf.mono (by norm_num)) (by norm_num)
    refine ⟨(eb_add hQ.1 (t2.mono (by norm_num)) (by norm_num)).congr ?_, (hQ.2.mono (by norm_num)).congr ?_⟩
    · simp
    · simp
  have s2 := eb_smt3K' (hD.mono (by norm_num)) (hQ.mono (by norm_num)) hQs (by norm_num) (by norm_num)
  have d3 := eb_dist hQ hR (by norm_num) (by norm_num)
  have t1 := eb_sub (e7.mono (by norm_num)) s1 (by norm_num)
  have t2 := eb_sub t1 (s2.mono (by norm_num)) (by norm_num)
  have t3 := eb_sub t2 (d3.mono (by norm_num)) (by norm_num)
  unfold psiY2PosK at h
  have hpos := posK_sound t3.2 h
  simp only [S43.Stmt.psiNet]
  rw [h1, h2]
  exact hpos

theorem lemmaK_Y_eq (st : Bool) (fval L : ℕ) (W : VarsK) (A Bp D U V Pp Q R sP r : PK) :
    lemmaK st fval L W A Bp D U V Pp Q R sP r .Y = lemY st fval W.b W.c W.d W.s W.e W.f A Bp D V Pp Q R r := rfl

theorem lemY_sound {st : Bool} {fval L : ℕ} {b c d s e f : DN} {A Bp D V Pp Q R r : PK} {w : S43.Stmt.Vars}
    (hb : EB 126 b w.b) (hc : EB 126 c w.c) (hd : EB 126 d w.d) (hs : EB 126 s w.s) (he : EB 126 e w.e)
    (hf : EB 126 f w.f) (hA : PB 135 A (S43.Stmt.pts w).A) (hB : PB 135 Bp (S43.Stmt.pts w).B)
    (hD : PB 135 D (S43.Stmt.pts w).D) (hV : st = true → PB 135 V (S43.Stmt.pts w).V)
    (hPp : PB 135 Pp (S43.Stmt.pts w).P) (hQ : PB 135 Q (S43.Stmt.pts w).Q) (hR : PB 135 R (S43.Stmt.pts w).R)
    (hr : PB 135 r (S43.Stmt.pts w).r) {z : DN} (h : lemY st fval b c d s e f A Bp D V Pp Q R r = some z) :
    (fval = 1 ∨ (famOf st = .reg ∧ fval = 3)) ∧
      ∃ cb, S43.Stmt.lemmaBound (famOf st) L .Y w = some cb ∧ EB 179 z cb.2 ∧
        ((famOf st = .reg ∧ fval = 3) → ∀ ω : S43.Stmt.Wit,
          ω.p1 = smt3PtK A Bp D (S43.Stmt.pts w).A (S43.Stmt.pts w).B (S43.Stmt.pts w).D →
          ω.p2 = smt3PtK D Q (psiQs c d f Q) (S43.Stmt.pts w).D (S43.Stmt.pts w).Q
            ((S43.Stmt.pts w).Q + (2 * w.d + w.c - w.f)) →
          0 < S43.Stmt.psiNet w ω) := by
  unfold lemY at h
  cases st
  · by_cases h3 : fval = 3
    · subst h3
      rw [show (Nat.beq 3 3 && !false) = true from rfl, Bool.cond_true] at h
      cases hp : psiY2PosK b c d s e f A Bp D Q R
      · rw [hp, Bool.cond_false] at h; exact absurd h (by simp)
      · rw [hp, Bool.cond_true] at h
        have hz := Option.some.inj h
        refine ⟨Or.inr ⟨rfl, rfl⟩, _, rfl, ?_, ?_⟩
        · rw [← hz]; exact eb_maxd2 hD hPp hQ
        · intro _ ω h1 h2; exact psiY2PosK_gen hb hc hd hs he hf hA hB hD hQ hR hp h1 h2
    · rw [nbeq_false h3, Bool.false_and, Bool.cond_false] at h
      by_cases h1 : fval = 1
      · subst h1
        rw [show (!(Nat.beq 1 1)) = false from rfl, Bool.cond_false, Bool.cond_false] at h
        have hz := Option.some.inj h
        refine ⟨Or.inl rfl, _, rfl, ?_, ?_⟩
        · rw [← hz]; exact eb_maxd2 hD hPp hQ
        · rintro ⟨-, h3'⟩; exact absurd h3' (by omega)
      · rw [nbeq_false h1, Bool.not_false, Bool.cond_true] at h; exact absurd h (by simp)
  · rw [Bool.not_true, Bool.and_false, Bool.cond_false] at h
    by_cases h1 : fval = 1
    · subst h1
      rw [show (!(Nat.beq 1 1)) = false from rfl, Bool.cond_false, Bool.cond_true] at h
      have hz := Option.some.inj h
      refine ⟨Or.inl rfl, _, rfl, ?_, ?_⟩
      · rw [← hz]; exact eb_maxd3 (hV rfl) hr hPp hQ
      · rintro ⟨h', -⟩; exact absurd h' (by simp [famOf])
    · rw [nbeq_false h1, Bool.not_false, Bool.cond_true] at h; exact absurd h (by simp)

theorem lemmaK_eq (st : Bool) (fval L : ℕ) (W : VarsK) (A Bp D U V Pp Q R sP r : PK) (K : KeyK) :
    lemmaK st fval L W A Bp D U V Pp Q R sP r K =
      lemmaV st fval L W.b W.c W.d W.s W.e W.f A Bp D U V Pp Q R sP r K := rfl

/-- the AX entry for the lemmas 0, 1, 2, 5, 8 -/
theorem lemAX_sound {L : ℕ} {c e f s : DN} {A sP r Pp R : PK} {w : S43.Stmt.Vars} {F : S43.Stmt.Fam}
    (hc : EB 126 c w.c) (he : EB 126 e w.e) (hf : EB 126 f w.f) (hs : EB 126 s w.s)
    (hA : PB 135 A (S43.Stmt.pts w).A) (hsP : PB 135 sP (S43.Stmt.pts w).s) (hr : PB 135 r (S43.Stmt.pts w).r)
    (hPp : PB 135 Pp (S43.Stmt.pts w).P) (hR : PB 135 R (S43.Stmt.pts w).R)
    (hL : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 5 ∨ L = 8) {z : DN} (h : lemAX L c e f s A sP r Pp R = some z) :
    S43.Stmt.avail F L .AX = true ∧ ∃ cb, S43.Stmt.lemmaBound F L .AX w = some cb ∧ cb.1 ∧ EB 179 z cb.2 := by
  have hce : EB 127 (DN.add c e) (w.c + w.e) := eb_add hc he (by norm_num)
  have hm : EB 130 (DN.half (DN.mul (DN.sub (DN.add c e) DN.one) SQ3)) ((w.c + w.e - 1) * Real.sqrt 3 / 2) := by
    have t1 := eb_sub hce (eb_one.mono (by norm_num)) (by norm_num)
    have t2 := eb_mul t1 eb_SQ3 (by norm_num) (by norm_num)
    exact eb_half t2 (by norm_num)
  have hm' : EB 130 (DN.half (DN.mul (DN.sub (DN.add c e) DN.one) SQ3)) (Real.sqrt 3 / 2 * (w.c + w.e - 1)) :=
    hm.congr (by ring)
  unfold lemAX at h
  rcases hL with rfl | rfl | rfl | rfl | rfl
  · -- lemma 0
    rw [show Nat.beq 0 0 = true from rfl, Bool.cond_true] at h
    unfold lemAX0 at h
    cases hq : DN.lec c DN.one
    · rw [hq, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hq, Bool.cond_true] at h
      have hz := Option.some.inj h
      refine ⟨rfl, _, rfl, lecK_sound hc.2 eb_one.2 hq, ?_⟩
      rw [← hz]; exact eb_maxd2 hA hr hPp
  · -- lemma 1
    rw [show Nat.beq 1 0 = false from rfl, Bool.cond_false, show Nat.beq 1 5 = false from rfl, Bool.cond_false,
      show Nat.beq 1 8 = false from rfl, Bool.cond_false] at h
    unfold lemAX12 at h
    rw [show Nat.beq 1 1 = true from rfl, Bool.cond_true] at h
    unfold lemAX12b at h
    have ha : EB 129 (DN.add (DN.sub (DN.nmul2 (DN.divD s SQ3)) c) DN.one) (2 * (w.s / Real.sqrt 3) - w.c + 1) := by
      have t1 := eb_divSQ3 hs (by norm_num)
      have t2 := eb_nmul2 t1 (by norm_num)
      have t3 := eb_sub t2 (hc.mono (by norm_num)) (by norm_num)
      exact eb_add t3 (eb_one.mono (by norm_num)) (by norm_num)
    cases hq : (DN.ltc e (DN.add (DN.sub (DN.nmul2 (DN.divD s SQ3)) c) DN.one) && DN.gec (DN.add c e) DN.one)
    · rw [hq, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hq, Bool.cond_true] at h
      rw [Bool.and_eq_true] at hq
      obtain ⟨q1, q2⟩ := hq
      have c1 := ltcK_sound he.2 ha.2 q1
      have c2 := gecK_sound hce.2 eb_one.2 q2
      have hz := Option.some.inj h
      refine ⟨rfl, _, rfl, ⟨?_, c2⟩, ?_⟩
      · have : 2 * (w.s / Real.sqrt 3) = 2 / Real.sqrt 3 * w.s := by ring
        linarith
      · rw [← hz]
        exact eb_max (eb_maxd4 hA hsP hr hPp hR) (hm'.mono (by norm_num))
  · -- lemma 2
    rw [show Nat.beq 2 0 = false from rfl, Bool.cond_false, show Nat.beq 2 5 = false from rfl, Bool.cond_false,
      show Nat.beq 2 8 = false from rfl, Bool.cond_false] at h
    unfold lemAX12 at h
    rw [show Nat.beq 2 1 = false from rfl, Bool.cond_false] at h
    unfold lemAX12b at h
    have ha : EB 128 (DN.add (DN.mul TWO_OVER_SQ3_M1 c) DN.one) ((2 / Real.sqrt 3 - 1) * w.c + 1) := by
      have t1 := eb_mul eb_two_over hc (by norm_num) (by norm_num)
      exact eb_add t1 (eb_one.mono (by norm_num)) (by norm_num)
    cases hq : (DN.ltc e (DN.add (DN.mul TWO_OVER_SQ3_M1 c) DN.one) && DN.gec (DN.add c e) DN.one)
    · rw [hq, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hq, Bool.cond_true] at h
      rw [Bool.and_eq_true] at hq
      obtain ⟨q1, q2⟩ := hq
      have c1 := ltcK_sound he.2 ha.2 q1
      have c2 := gecK_sound hce.2 eb_one.2 q2
      have hz := Option.some.inj h
      refine ⟨rfl, _, rfl, ⟨by linarith, c2⟩, ?_⟩
      rw [← hz]
      exact eb_max (eb_maxd4 hA hsP hr hPp hR) (hm'.mono (by norm_num))
  · -- lemma 5
    rw [show Nat.beq 5 0 = false from rfl, Bool.cond_false, show Nat.beq 5 5 = true from rfl, Bool.cond_true] at h
    unfold lemAX5 at h
    cases hq : x2Cond c e f (DN.mul TWO_OVER_SQ3_M1 c)
    · rw [hq, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hq, Bool.cond_true] at h
      have hz := Option.some.inj h
      refine ⟨rfl, _, rfl, x2CondK_sound hc he hf hq, ?_⟩
      rw [← hz]; exact eb_maxd3 hA hr hPp hR
  · -- lemma 8
    rw [show Nat.beq 8 0 = false from rfl, Bool.cond_false, show Nat.beq 8 5 = false from rfl, Bool.cond_false,
      show Nat.beq 8 8 = true from rfl, Bool.cond_true] at h
    unfold lemAX8 at h
    cases hq : DN.ltc e (DN.add s DN.one)
    · rw [hq, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hq, Bool.cond_true] at h
      have hz := Option.some.inj h
      have hs1 : EB 127 (DN.add s DN.one) (w.s + 1) := eb_add hs (eb_one.mono (by norm_num)) (by norm_num)
      have hec : EB 128 (DN.sub (DN.add e c) DN.one) (w.e + w.c - 1) :=
        eb_sub (eb_add he hc (by norm_num)) (eb_one.mono (by norm_num)) (by norm_num)
      refine ⟨rfl, _, rfl, ltcK_sound he.2 hs1.2 hq, ?_⟩
      rw [← hz]; exact eb_max (eb_maxd3 hA hr hPp hR) (hec.mono (by norm_num))

/-- lemma 5's U/V/D entry at the point `Wp` -/
theorem lemW5_sound {c e f : DN} {Wp r Pp R : PK} {w : S43.Stmt.Vars} {zW : ℂ}
    (hc : EB 126 c w.c) (he : EB 126 e w.e) (hf : EB 126 f w.f) (hW : PB 135 Wp zW)
    (hr : PB 135 r (S43.Stmt.pts w).r) (hPp : PB 135 Pp (S43.Stmt.pts w).P) (hR : PB 135 R (S43.Stmt.pts w).R)
    {z : DN} (h : lemW5 c e f Wp r Pp R = some z) :
    S43.Stmt.cond5 w ∧ EB 179 z (max (S43.Stmt.maxdist zW [(S43.Stmt.pts w).r, (S43.Stmt.pts w).P, (S43.Stmt.pts w).R])
      (S43.Stmt.dist zW ((S43.Stmt.pts w).R - ((w.c : ℂ) - w.e) / 2 * S43.Stmt.dir2))) := by
  unfold lemW5 at h
  cases hq : x2Cond c e f (DN.mul TWO_OVER_SQ3_M1 c)
  · rw [hq, Bool.cond_false] at h; exact absurd h (by simp)
  · rw [hq, Bool.cond_true] at h
    unfold lemW5b at h
    have hz := Option.some.inj h
    refine ⟨x2CondK_sound hc he hf hq, ?_⟩
    rw [← hz]
    exact eb_max (eb_maxd3 hW hr hPp hR)
      (eb_dist (hW.mono (by norm_num)) (pb_hPt hR hc he) (by norm_num) (by norm_num))

theorem lemmaV_X_sound {st : Bool} {fval L : ℕ} {b c d s e f : DN} {A Bp D U V Pp Q R sP r : PK}
    {w : S43.Stmt.Vars} (hc : EB 126 c w.c) (he : EB 126 e w.e) (hf : EB 126 f w.f) (hs : EB 126 s w.s)
    (hA : PB 135 A (S43.Stmt.pts w).A) (hD : PB 135 D (S43.Stmt.pts w).D)
    (hU : st = true → PB 135 U (S43.Stmt.pts w).U) (hV : st = true → PB 135 V (S43.Stmt.pts w).V)
    (hPp : PB 135 Pp (S43.Stmt.pts w).P) (hR : PB 135 R (S43.Stmt.pts w).R) (hsP : PB 135 sP (S43.Stmt.pts w).s)
    (hr : PB 135 r (S43.Stmt.pts w).r) {K : KeyK} (hK : K ≠ .Y) (hav : availK st L K = true) {z : DN}
    (h : lemmaV st fval L b c d s e f A Bp D U V Pp Q R sP r K = some z) :
    S43.Stmt.avail (famOf st) L (keyToN K) = true ∧
      ∃ cb, S43.Stmt.lemmaBound (famOf st) L (keyToN K) w = some cb ∧ cb.1 ∧ EB 179 z cb.2 := by
  cases K
  · have hL : L = 0 ∨ L = 1 ∨ L = 2 ∨ L = 5 ∨ L = 8 := by
      simp only [availK, Bool.or_eq_true, Nat.beq_eq] at hav; omega
    exact lemAX_sound hc he hf hs hA hsP hr hPp hR hL h
  · cases st
    · simp [availK] at hav
    · have hL : L = 5 := by simpa [availK] using hav
      subst hL
      obtain ⟨c5, hz⟩ := lemW5_sound hc he hf (hU rfl) hr hPp hR h
      exact ⟨rfl, _, rfl, c5, hz⟩
  · cases st
    · simp [availK] at hav
    · have hL : L = 5 := by simpa [availK] using hav
      subst hL
      obtain ⟨c5, hz⟩ := lemW5_sound hc he hf (hV rfl) hr hPp hR h
      exact ⟨rfl, _, rfl, c5, hz⟩
  · cases st
    · have hL : L = 5 := by simpa [availK] using hav
      subst hL
      obtain ⟨c5, hz⟩ := lemW5_sound hc he hf hD hr hPp hR h
      exact ⟨rfl, _, rfl, c5, hz⟩
    · simp [availK] at hav
  · exact absurd rfl hK

/-! ## End of helper lemmas -/

/-! ## A. Lemma Y2's Psi (mirror of `psiY2PosN_sound`) -/

theorem psiY2PosK_sound {st : Bool} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w)
    (hP : PtsEncK st (ptsK st W) w)
    (h : psiY2PosK W.b W.c W.d W.s W.e W.f (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).Q
      (ptsK st W).R = true)
    {ω : S43.Stmt.Wit}
    (h1 : ω.p1 = smt3PtK (ptsK st W).A (ptsK st W).B (ptsK st W).D (S43.Stmt.pts w).A (S43.Stmt.pts w).B
      (S43.Stmt.pts w).D)
    (h2 : ω.p2 = smt3PtK (ptsK st W).D (ptsK st W).Q (psiQs W.c W.d W.f (ptsK st W).Q) (S43.Stmt.pts w).D
      (S43.Stmt.pts w).Q ((S43.Stmt.pts w).Q + (2 * w.d + w.c - w.f))) :
    0 < S43.Stmt.psiNet w ω := by
  obtain ⟨hb, hc, hd, hs, he, hf, -⟩ := hW
  exact psiY2PosK_gen hb hc hd hs he hf hP.A hP.B hP.D hP.Q hP.R h h1 h2

/-! ## B. The X lemma entries (mirror of `lemmaEntry_sound`) -/

theorem lemmaK_sound_X {st : Bool} {fval L : ℕ} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w)
    (hP : PtsEncK st (ptsK st W) w) {K : KeyK} (hK : K ≠ .Y) (hav : availK st L K = true) {z : DN}
    (h : lemmaK st fval L W (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
      (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r K = some z) :
    S43.Stmt.avail (famOf st) L (keyToN K) = true ∧
      ∃ cb, S43.Stmt.lemmaBound (famOf st) L (keyToN K) w = some cb ∧ cb.1 ∧ EB 179 z cb.2 := by
  obtain ⟨hb, hc, hd, hs, he, hf, -⟩ := hW
  rw [lemmaK_eq] at h
  exact lemmaV_X_sound hc he hf hs hP.A hP.D hP.U hP.V hP.P hP.R hP.s hP.r hK hav h

/-! ## C. The Y entry -/

theorem lemmaK_sound_Y {st : Bool} {fval L : ℕ} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w)
    (hP : PtsEncK st (ptsK st W) w) {z : DN}
    (h : lemmaK st fval L W (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
      (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r .Y = some z) :
    (fval = 1 ∨ (famOf st = .reg ∧ fval = 3)) ∧
      ∃ cb, S43.Stmt.lemmaBound (famOf st) L .Y w = some cb ∧ EB 179 z cb.2 ∧
        ((famOf st = .reg ∧ fval = 3) → ∀ ω : S43.Stmt.Wit,
          ω.p1 = smt3PtK (ptsK st W).A (ptsK st W).B (ptsK st W).D (S43.Stmt.pts w).A (S43.Stmt.pts w).B
            (S43.Stmt.pts w).D →
          ω.p2 = smt3PtK (ptsK st W).D (ptsK st W).Q (psiQs W.c W.d W.f (ptsK st W).Q) (S43.Stmt.pts w).D
            (S43.Stmt.pts w).Q ((S43.Stmt.pts w).Q + (2 * w.d + w.c - w.f)) →
          0 < S43.Stmt.psiNet w ω) := by
  obtain ⟨hb, hc, hd, hs, he, hf, -⟩ := hW
  rw [lemmaK_Y_eq] at h
  exact lemY_sound hb hc hd hs he hf hP.A hP.B hP.D hP.V hP.P hP.Q hP.R hP.r h

/-! ## D. Term and S+ kinds: kernel = lean/ -/

/-! Helpers for D -/

theorem allLt_memD {n : ℕ} : ∀ {l : List ℕ}, allLt n l = true → ∀ i ∈ l, i < n
  | [], _, i, hi => by simp at hi
  | a :: l, h, i, hi => by
    simp only [allLt, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact h.1
    · exact allLt_memD h.2 i hi

theorem nnD (st : Bool) : nXK st = S43.Stmt.nn (famOf st) := by cases st <;> rfl

theorem nbeq_falseD {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := by
  cases e : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem availK_eqD (st : Bool) (L : ℕ) (K : KeyK) : availK st L K = S43.Stmt.avail (famOf st) L (keyToN K) := by
  rw [Bool.eq_iff_iff]
  cases st <;> cases K <;> simp [availK, S43.Stmt.avail, keyToN, famOf] <;> omega

theorem edgeKeyK_mapD (st : Bool) (a b : ℕ) : (edgeKeyK st a b).map keyToN = S43.Stmt.edgeKey (famOf st) a b := by
  cases st <;>
  simp only [edgeKeyK, edgeKey2, edgeKeyX, nXK, nYK, S43.Stmt.edgeKey, S43.edgeKey, famOf, S43.Stmt.ids,
    S43.idsSt, S43.idsReg, Bool.cond_true, Bool.cond_false, Bool.cond_eq_ite, Nat.beq_eq, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, ↓reduceIte] <;>
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all

theorem tKindK_mapD (st : Bool) (L a b : ℕ) : (tKindK st L a b).map tkToN = S43.Stmt.tKind (famOf st) L a b := by
  have hX : nXK st = (S43.Stmt.ids (famOf st)).nX := by cases st <;> rfl
  have hY : nYK st = (S43.Stmt.ids (famOf st)).nY := by cases st <;> rfl
  unfold tKindK S43.Stmt.tKind
  try dsimp only
  by_cases hP : a = (S43.Stmt.ids (famOf st)).nX ∨ b = (S43.Stmt.ids (famOf st)).nX ∨
      a = (S43.Stmt.ids (famOf st)).nY ∨ b = (S43.Stmt.ids (famOf st)).nY
  · have hc : (Nat.beq a (nXK st) || Nat.beq b (nXK st) || Nat.beq a (nYK st) || Nat.beq b (nYK st)) = true := by
      rw [hX, hY]; rcases hP with e | e | e | e <;> simp [e, Nat.beq_refl]
    rw [hc, Bool.cond_true, if_pos hP, ← edgeKeyK_mapD]
    unfold tKindX
    cases edgeKeyK st a b with
    | none => rfl
    | some K =>
      show Option.map tkToN (bif availK st L K then some (TK.bnd K) else none) =
        (if S43.Stmt.avail (famOf st) L (keyToN K) = true then some (S43.Stmt.TermK.bnd (keyToN K)) else none)
      rw [← availK_eqD]
      cases availK st L K <;> rfl
  · have hc : (Nat.beq a (nXK st) || Nat.beq b (nXK st) || Nat.beq a (nYK st) || Nat.beq b (nYK st)) = false := by
      rw [hX, hY]
      simp only [not_or] at hP
      obtain ⟨h1, h2, h3, h4⟩ := hP
      rw [nbeq_falseD h1, nbeq_falseD h2, nbeq_falseD h3, nbeq_falseD h4]; rfl
    rw [hc, Bool.cond_false, if_neg hP]
    by_cases hQ : a < S43.Stmt.nn (famOf st) ∧ b < S43.Stmt.nn (famOf st)
    · have hd : (Nat.blt a (nXK st) && Nat.blt b (nXK st)) = true := by
        rw [nnD]; simp [Nat.blt_eq, hQ.1, hQ.2]
      rw [hd, Bool.cond_true, if_pos hQ]; rfl
    · have hd : (Nat.blt a (nXK st) && Nat.blt b (nXK st)) = false := by
        rw [nnD]
        cases e1 : Nat.blt a (S43.Stmt.nn (famOf st)) <;> cases e2 : Nat.blt b (S43.Stmt.nn (famOf st)) <;> try rfl
        exact absurd ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2⟩ hQ
      rw [hd, Bool.cond_false, if_neg hQ]; rfl

theorem tKindsK_mapD {st : Bool} {L : ℕ} : ∀ (ta tb : List ℕ) (ts : List TK), tKindsK st L ta tb = some ts →
    (List.zipWith (S43.Stmt.tKind (famOf st) L) ta tb).mapM id = some (ts.map tkToN)
  | [], _, ts, h => by simp [tKindsK] at h; subst h; simp
  | _ :: _, [], ts, h => by simp [tKindsK] at h; subst h; simp
  | a :: as, b :: bs, ts, h => by
    simp only [tKindsK] at h
    unfold consT at h
    split at h
    · rename_i t ts' h1 h2
      simp only [Option.some.injEq] at h; subst h
      have e1 := tKindK_mapD st L a b
      rw [h1, Option.map_some] at e1
      simp only [List.zipWith_cons_cons, List.mapM_cons, id, ← e1, tKindsK_mapD as bs ts' h2]
      simp
    · exact absurd h (by simp)

theorem srtD_reg1 : S43.sorted4 [0, 2, 4, 5] = [0, 2, 4, 5] := List.mergeSort_of_pairwise (by decide)

theorem srtD_reg2 : S43.sorted4 [1, 2, 4, 5] = [1, 2, 4, 5] := List.mergeSort_of_pairwise (by decide)

theorem srtD_st1 : S43.sorted4 [0, 2, 6, 7] = [0, 2, 6, 7] := List.mergeSort_of_pairwise (by decide)

theorem srtD_st2 : S43.sorted4 [1, 2, 6, 7] = [1, 2, 6, 7] := List.mergeSort_of_pairwise (by decide)


theorem tKindsK_sound {st : Bool} {L : ℕ} {sp : SplitK} {ts : List TK} (h : tKindsK st L sp.ta sp.tb = some ts) :
    S43.Stmt.tKinds (famOf st) L (toSplit sp) = some (ts.map tkToN) := by
  unfold S43.Stmt.tKinds toSplit
  simp only [List.toList_toArray]
  exact tKindsK_mapD _ _ _ h

theorem spKindK_sound {st : Bool} {L : ℕ} {sp : SplitK} {sk : SK} (h : spKindK st L sp.sp = some sk) :
    S43.Stmt.spKind (famOf st) L (toSplit sp) = some (skToN sk) := by
  unfold spKindK at h
  cases hal : allLt (nXK st) sp.sp
  · rw [hal, Bool.cond_false] at h; exact absurd h (by simp)
  · rw [hal, Bool.cond_true] at h
    have hlt := allLt_memD hal
    rw [nnD] at hlt
    have hall : sp.sp.all (· < S43.Stmt.nn (famOf st)) = true :=
      List.all_eq_true.2 fun i hi => by simpa using hlt i hi
    unfold S43.Stmt.spKind
    simp only [toSplit, List.toList_toArray, hall, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize sp.sp = l at h ⊢
    match l, h with
    | [], h => simp only [spKindL, Option.some.injEq] at h; subst h; rfl
    | [_], h => simp only [spKindL, Option.some.injEq] at h; subst h; rfl
    | [a, b], h => simp only [spKindL, Option.some.injEq] at h; subst h; rfl
    | [a, b, c], h => simp only [spKindL, Option.some.injEq] at h; subst h; rfl
    | [a, b, c, d], h =>
      simp only [spKindL] at h
      cases st <;>
      simp only [spKind4, eq4, Bool.cond_true, Bool.cond_false, Bool.cond_eq_ite, Bool.and_eq_true,
        Bool.or_eq_true, Nat.beq_eq] at h <;>
      simp only [famOf, S43.Stmt.ids, S43.idsSt, S43.idsReg, srtD_reg1, srtD_reg2, srtD_st1, srtD_st2,
        List.cons.injEq, and_true] <;>
      split_ifs at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      (split_ifs <;> first | rfl | (exfalso; omega) | simp_all)
    | _ :: _ :: _ :: _ :: _ :: _, h => simp [spKindL] at h

/-- the kinds' node ids are positioned nodes -/
theorem tKindK_seg_lt {st : Bool} {L a b i j : ℕ} (h : tKindK st L a b = some (.seg i j)) :
    i < S43.Stmt.nn (famOf st) ∧ j < S43.Stmt.nn (famOf st) := by
  unfold tKindK at h
  cases hc : (Nat.beq a (nXK st) || Nat.beq b (nXK st) || Nat.beq a (nYK st) || Nat.beq b (nYK st))
  · rw [hc, Bool.cond_false] at h
    cases hd : (Nat.blt a (nXK st) && Nat.blt b (nXK st))
    · rw [hd, Bool.cond_false] at h; exact absurd h (by simp)
    · rw [hd, Bool.cond_true] at h
      simp only [Option.some.injEq, TK.seg.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, Nat.blt_eq] at hd
      rw [← nnD]; exact hd
  · rw [hc, Bool.cond_true] at h
    unfold tKindX at h
    split at h
    · exact absurd h (by simp)
    · rename_i K' _
      cases hav : availK st L K'
      · rw [hav, Bool.cond_false] at h; exact absurd h (by simp)
      · rw [hav, Bool.cond_true] at h; exact absurd h (by simp)

theorem spKindK_lt {st : Bool} {L : ℕ} {l : List ℕ} {sk : SK} (h : spKindK st L l = some sk) :
    ∀ i ∈ l, i < S43.Stmt.nn (famOf st) := by
  unfold spKindK at h
  cases hal : allLt (nXK st) l
  · rw [hal, Bool.cond_false] at h; exact absurd h (by simp)
  · rw [← nnD]; exact allLt_memD hal

/-! ## E. Node selection -/

theorem pb_ptSel {st : Bool} {W : VarsK} {w : S43.Stmt.Vars} (hP : PtsEncK st (ptsK st W) w) {i : ℕ}
    (hi : i < S43.Stmt.nn (famOf st)) :
    PB 135 (ptSel st i (ptsK st W).A (ptsK st W).B (ptsK st W).D (ptsK st W).U (ptsK st W).V (ptsK st W).P
      (ptsK st W).Q (ptsK st W).R (ptsK st W).s (ptsK st W).r) (S43.Stmt.pt (famOf st) w i) := by
  exact pb_ptSel_gen hP hi

/-! ## F. The S- sum (mirror of `smDIN`; the list length bound comes from the split literals) -/

theorem eb_smSum {st : Bool} {W : VarsK} {w : S43.Stmt.Vars} (hW : VEncK st W w) {sp : SplitK}
    (hlen : sp.sm.length ≤ 40) :
    EB 166 (smSum st W sp.sm DN.zero) (S43.Stmt.sMinus (famOf st) (toSplit sp) w) := by
  have h0 : EB 126 DN.zero 0 := eb_zero.mono (by norm_num)
  have := eb_smSum_aux hW sp.sm 126 DN.zero 0 (le_refl _) (by omega) h0
  have e : S43.Stmt.sMinus (famOf st) (toSplit sp) w =
      (sp.sm.map fun i => if i = 0 then (1 : ℝ) else S43.Stmt.varOf (famOf st) w (i - 1)).sum := by
    unfold S43.Stmt.sMinus toSplit
    rfl
  rw [e]
  exact (this.mono (by omega)).congr (by ring)

end S43K

end
