module

public import S43.Sound.Case

@[expose] public section

/-! # The Steiner ratio bound from the certificate theorem and the lemma layer

`HDuHwang` asks, for every realized configuration, for a split whose bound with the true trapped-point distances is
`≤ 0`. The certificate gives a split whose bound with the lemma bounds is `≤ 0`; `HTrap` bounds each true trapped-point
distance by its lemma bound (`tTrue_le`), and `HDomain` puts realized coordinates in the case domain. -/

namespace S43.Stmt

theorem sum_le_of_mapM {α β : Type} (f : α → β → Option (Prop × ℝ)) (g : α → β → ℝ)
    (hfg : ∀ a b e, f a b = some e → e.1 → g a b ≤ e.2) :
    ∀ (xs : List α) (ys : List β) (es : List (Prop × ℝ)), (List.zipWith f xs ys).mapM id = some es →
      (∀ e ∈ es, e.1) → (List.zipWith g xs ys).sum ≤ (es.map Prod.snd).sum := by
  intro xs
  induction xs with
  | nil => intro ys es h _; simp at h; subst h; simp
  | cons x xs ih =>
    intro ys es h hc
    cases ys with
    | nil => simp at h; subst h; simp
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mapM_cons, id] at h
      cases hf : f x y with
      | none => simp [hf] at h
      | some e =>
        cases hr : (List.zipWith f xs ys).mapM id with
        | none => simp [hf, hr] at h
        | some es' =>
          simp [hf, hr] at h
          subst h
          simp only [List.zipWith_cons_cons, List.sum_cons, List.map_cons]
          have h1 := hfg x y e hf (hc e List.mem_cons_self)
          have h2 := ih ys es' hr (fun e' he' => hc e' (List.mem_cons_of_mem _ he'))
          linarith

theorem mapM_zipWith_isSome {α β γ : Type} (f : α → β → Option γ) :
    ∀ (xs : List α) (ys : List β) (es : List γ), (List.zipWith f xs ys).mapM id = some es →
      ∀ i (h1 : i < xs.length) (h2 : i < ys.length), (f xs[i] ys[i]).isSome := by
  intro xs
  induction xs with
  | nil => intro ys es _ i h1; simp at h1
  | cons x xs ih =>
    intro ys es h i h1 h2
    cases ys with
    | nil => simp at h2
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mapM_cons, id] at h
      cases hf : f x y with
      | none => simp [hf] at h
      | some e =>
        cases hr : (List.zipWith f xs ys).mapM id with
        | none => simp [hf, hr] at h
        | some es' =>
          rcases i with _ | i
          · simp [hf]
          · simpa using ih ys es' hr i (by simpa using h1) (by simpa using h2)

theorem main_of_certificate {ρ : ℝ} (hρ : 0 ≤ ρ) (hsz : ∀ F, ∀ sp ∈ splits F, sp.ta.size = sp.tb.size)
    (hcert : ∀ F w, domain F w → ∃ sp ∈ splits F, ∃ L ≤ 8, certifies F sp L ρ w)
    (Real : Realized) (htrap : HTrap Real) (hdom : HDomain Real) (hdh : HDuHwang Real ρ) :
    ∀ P : Finset ℂ, ρ * mstLength P ≤ steinerLength P := by
  apply hdh
  intro F w X Y hR
  obtain ⟨sp, hsp, L, -, es, hes, hcond, hle⟩ := hcert F w (hdom F w X Y hR)
  refine ⟨sp, hsp, ?_, ?_⟩
  · -- every edge to X or Y has a key
    intro i hi a b I hxy
    have hsome := mapM_zipWith_isSome _ _ _ _ hes i (by simpa using hi) (by simpa [← hsz F sp hsp] using hi)
    have ha : sp.ta.toList[i]'(by simpa using hi) = a := by simp [a, getElem!_pos sp.ta i hi]
    have hb : sp.tb.toList[i]'(by simpa [← hsz F sp hsp] using hi) = b := by
      simp [b, getElem!_pos sp.tb i (by rw [← hsz F sp hsp]; exact hi)]
    rw [ha, hb] at hsome
    unfold tEdge at hsome
    simp only at hsome
    rw [if_pos hxy] at hsome
    cases hk : edgeKey F a b with
    | none => rw [hk] at hsome; simp at hsome
    | some K => rfl
  · -- the true lengths are at most the certified bounds
    have key : tTrue F sp w X Y ≤ (es.map Prod.snd).sum := by
      unfold tTrue
      refine sum_le_of_mapM (tEdge F L w) _ (fun a b e he hc => ?_) _ _ _ hes hcond
      unfold tEdge at he
      simp only at he ⊢
      split_ifs at he ⊢ with hxy
      · cases hk : edgeKey F a b with
        | none => rw [hk] at he; simp at he
        | some K =>
          rw [hk] at he
          simp only [Option.bind_some] at he
          exact htrap F w X Y L K hR e he hc
      · cases h1 : nodePt F w a with
        | none => rw [h1] at he; simp at he
        | some x =>
          cases h2 : nodePt F w b with
          | none => rw [h1, h2] at he; simp at he
          | some y =>
            rw [h1, h2] at he
            simp only [Option.some.injEq] at he
            subst he
            simp
    have := mul_le_mul_of_nonneg_left key hρ
    linarith

end S43.Stmt

end
