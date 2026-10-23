import S43.Sound.Record

/-! # Facts about the published split lists, as Boolean checks

`monoCheck F fval = true` gives `MonoData F fval`: the monotonicity masks of the tables (computed by `checker/mono43.py`) imply the
monotonicity rule `monoRule` wherever the checker uses them (unbounded sides of lemma-0 records, f := d, the extension rule
of the subcase f ≥ d). `sizeCheck` says every split has as many T* left ends as right ends. Both are decided by
`native_decide` in `S43.Final`. -/

namespace S43

open Stmt

def monoCheck (F : Fam) (fval : ℕ) : Bool :=
  (splits F).toList.all fun sp => (List.range 9).all fun L =>
    match tKinds F L sp, spKind F L sp with
    | some ks, some sk =>
      (!(fval == 2 && bit sp.mono (ids F).vf) || monoRule F L .f sp ks sk) &&
      (L != 0 || (List.range (nbOf F fval)).all fun j =>
        (fval == 3 && j == (ids F).vf) || !bit sp.mono j || monoRule F 0 (vrOf F j) sp ks sk) &&
      (!(fval == 3 && !hasY (ids F) sp && extOK (ids F) sp) || monoRule F L .f sp ks sk)
    | _, _ => true

theorem monoData_of_check {F : Fam} {fval : ℕ} (h : monoCheck F fval = true) : MonoData F fval := by
  intro sp hsp L hL ks sk hks hsk
  unfold monoCheck at h
  rw [List.all_eq_true] at h
  have h1 := h sp (by simpa using hsp)
  rw [List.all_eq_true] at h1
  have h2 := h1 L (List.mem_range.mpr (by omega))
  rw [hks, hsk] at h2
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h2
  obtain ⟨⟨ha, hb⟩, hc⟩ := h2
  refine ⟨fun e hbit => ?_, fun e j hj hn hbit => ?_, fun e hy hx => ?_⟩
  · rcases ha with ha | ha
    · simp [e, hbit] at ha
    · exact ha
  · rcases hb with hb | hb
    · exact absurd e hb
    · rw [List.all_eq_true] at hb
      have := hb j (List.mem_range.mpr hj)
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
      rcases this with (h3 | h3) | h3
      · exact absurd h3 hn
      · simp [hbit] at h3
      · exact h3
  · rcases hc with hc | hc
    · simp [e, hy, hx] at hc
    · exact hc

def sizeCheck (F : Fam) : Bool := (splits F).toList.all fun sp => sp.ta.size == sp.tb.size

theorem size_of_check {F : Fam} (h : sizeCheck F = true) : ∀ sp ∈ splits F, sp.ta.size = sp.tb.size := by
  intro sp hsp
  unfold sizeCheck at h
  rw [List.all_eq_true] at h
  simpa using h sp (by simpa using hsp)

end S43
