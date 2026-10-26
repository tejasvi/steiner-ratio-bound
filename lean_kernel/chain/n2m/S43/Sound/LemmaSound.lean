module

public import S43.Sound.VertexSound

@[expose] public section

/-! # Soundness of the lemma entries for A-X, U-X, V-X, D-X edges

The checker's `lemmaEntry` (`S43Core.Geom`) for the published lemmas 0, 1, 2, 5, 8 and lemma 5's U/V/D bounds:
an accepted entry means the statement's `lemmaBound` exists, its condition holds and the interval encloses its bound. -/

namespace S43

attribute [local irreducible] P

open DI

/-- the statement's key of a checker key (`S43.Stmt.edgeKey`) -/
def keyMap : Key → Option Stmt.Key
  | .AX => some .AX | .UX => some .UX | .VX => some .VX | .DX => some .DX | .Y => some .Y | _ => none

theorem stmt_edgeKey (F : Stmt.Fam) (a b : ℕ) : Stmt.edgeKey F a b = (S43.edgeKey (Stmt.ids F) a b).bind keyMap := by
  unfold Stmt.edgeKey; first | rfl | (congr 1; funext K; cases K <;> rfl)

theorem enc_H {R : Pt} {zR : ℂ} (hR : PtEnc R zR) {c e : DI} {wc we : ℝ} (hc : c.Enc wc) (he : e.Enc we) :
    PtEnc (R.1 - (c - e).half.half, R.2 + (c - e).half.half * SQ3) (zR - ((wc : ℂ) - we) / 2 * Stmt.dir2) := by
  have hh := enc_half (enc_half (enc_sub hc he))
  refine ⟨Enc.congr (enc_sub hR.1 hh) ?_, Enc.congr (enc_add hR.2 (enc_mul hh enc_SQ3)) ?_⟩
  · simp [Stmt.dir2, Complex.mul_re] <;> ring
  · simp [Stmt.dir2, Complex.mul_im] <;> ring

theorem lemmaEntry_sound {F : Stmt.Fam} {fval L : ℕ} {V : Array DI} {P : Array Pt} {w : Stmt.Vars}
    (hV : VEnc F V w) (hP : PEnc F P w) {K : Key} {K' : Stmt.Key} (hK : keyMap K = some K') (hY : K' ≠ .Y) {z : DI}
    (h : lemmaEntry (Stmt.ids F) fval V P L K = some (some z)) :
    Stmt.avail F L K' = true ∧ ∃ cb, Stmt.lemmaBound F L K' w = some cb ∧ cb.1 ∧ z.Enc cb.2 := by
  obtain ⟨hb, hc, hd, hs, he, hf, huv⟩ := hV.get
  obtain ⟨nA, nB, nD, nP, nQ, nR, nS, nr, nUV⟩ := hP.nodes
  cases K <;> simp only [keyMap, Option.some.injEq, reduceCtorEq] at hK <;> subst hK
  · -- A-X
    rcases L with _ | _ | _ | _ | _ | _ | _ | _ | _ | L <;>
      simp +decide only [lemmaEntry, zero_add, Nat.reduceAdd, ↓reduceIte, reduceCtorEq] at h
    · -- lemma 0
      split_ifs at h with h1
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      have h1' : (V[(Stmt.ids F).vc]!).lec DI.one = true := by simpa using h1
      refine ⟨by simp [Stmt.avail], _, rfl, lec_sound hc enc_one h1', ?_⟩
      exact enc_maxdist P _ _ nA _ _ (by simp) (.cons nr (.cons nP .nil))
    · -- lemma 1
      split_ifs at h with h1
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      simp at h1
      obtain ⟨h1a, h1b⟩ := h1
      have ha := enc_add (enc_sub (enc_nmul 2 (enc_div_SQ3 hs)) hc) enc_one
      have c1 := ltc_sound he ha h1a
      have c2 := gec_sound (enc_add hc he) enc_one h1b
      refine ⟨by simp [Stmt.avail], _, rfl, ⟨?_, c2⟩, ?_⟩
      · push_cast at c1; linarith [show 2 * (w.s / √3) = 2 / √3 * w.s by ring]
      · refine Enc.congr (enc_max (enc_maxdist P _ _ nA _ _ (by simp) (.cons nS (.cons nr (.cons nP (.cons nR .nil)))))
          (enc_half (enc_mul (enc_sub (enc_add hc he) enc_one) enc_SQ3))) ?_
        congr 1; ring
    · -- lemma 2
      split_ifs at h with h1
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      simp at h1
      obtain ⟨h1a, h1b⟩ := h1
      have ha := enc_add (enc_mul enc_two_over hc) enc_one
      have c1 := ltc_sound he ha h1a
      have c2 := gec_sound (enc_add hc he) enc_one h1b
      refine ⟨by simp [Stmt.avail], _, rfl, ⟨by linarith, c2⟩, ?_⟩
      · refine Enc.congr (enc_max (enc_maxdist P _ _ nA _ _ (by simp) (.cons nS (.cons nr (.cons nP (.cons nR .nil)))))
          (enc_half (enc_mul (enc_sub (enc_add hc he) enc_one) enc_SQ3))) ?_
        congr 1; ring
    · -- lemma 5
      split_ifs at h with h1
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      have h1' := x2Cond_sound hc he hf (by simpa using h1)
      refine ⟨by simp [Stmt.avail], _, rfl, h1', ?_⟩
      exact enc_maxdist P _ _ nA _ _ (by simp) (.cons nr (.cons nP (.cons nR .nil)))
    · -- lemma 8
      split_ifs at h with h1
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      have h1' : (V[(Stmt.ids F).ve]!).ltc (V[(Stmt.ids F).vs]! + DI.one) = true := by simpa using h1
      have c1 := ltc_sound he (enc_add hs enc_one) h1'
      refine ⟨by simp [Stmt.avail], _, rfl, c1, ?_⟩
      exact enc_max (enc_maxdist P _ _ nA _ _ (by simp) (.cons nr (.cons nP (.cons nR .nil))))
        (enc_sub (enc_add he hc) enc_one)
  case Y => exact absurd rfl hY
  -- U-X, V-X, D-X: lemma 5 only
  all_goals
    rcases (show L = 5 ∨ L ≠ 5 by omega) with rfl | hL
    swap
    · simp [lemmaEntry, hL] at h
  · -- U-X
    cases F
    · simp +decide [lemmaEntry, Stmt.ids, idsReg] at h
    · obtain ⟨nU, _⟩ := nUV rfl
      simp +decide only [lemmaEntry, ↓reduceIte, Bool.false_eq_true] at h
      split_ifs at h with h3
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      have h3' := x2Cond_sound hc he hf (by simpa using h3)
      refine ⟨by simp [Stmt.avail], _, rfl, h3', ?_⟩
      exact enc_max (enc_maxdist P _ _ nU _ _ (by simp) (.cons nr (.cons nP (.cons nR .nil))))
        (enc_dist nU (enc_H nR hc he))
  · -- V-X
    cases F
    · simp +decide [lemmaEntry, Stmt.ids, idsReg] at h
    · obtain ⟨_, nV⟩ := nUV rfl
      simp +decide only [lemmaEntry, ↓reduceIte, Bool.false_eq_true] at h
      split_ifs at h with h3
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      have h3' := x2Cond_sound hc he hf (by simpa using h3)
      refine ⟨by simp [Stmt.avail], _, rfl, h3', ?_⟩
      exact enc_max (enc_maxdist P _ _ nV _ _ (by simp) (.cons nr (.cons nP (.cons nR .nil))))
        (enc_dist nV (enc_H nR hc he))
  · -- D-X
    cases F
    · simp +decide only [lemmaEntry, ↓reduceIte, Bool.false_eq_true] at h
      split_ifs at h with h3
      · simp at h
      simp only [Option.some.injEq] at h; subst h
      have h3' := x2Cond_sound hc he hf (by simpa using h3)
      refine ⟨by simp [Stmt.avail], _, rfl, h3', ?_⟩
      exact enc_max (enc_maxdist P _ _ nD _ _ (by simp) (.cons nr (.cons nP (.cons nR .nil))))
        (enc_dist nD (enc_H nR hc he))
    · simp +decide [lemmaEntry, Stmt.ids, idsSt] at h

end S43

end
