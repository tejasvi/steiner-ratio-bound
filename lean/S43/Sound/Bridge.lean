import S43.Sound.Unbounded

/-! # From the network semantics to the statement's `certifies`

`steinerLength P ≤` the length of any finite segment set connecting `P`; the explicit networks of the checker (segment,
star, two-Steiner-point network) connect their terminals. `bridge`: the network property at `(w, ω)` together with the
subcase conditions at `w` gives `certifies` for the split. -/

namespace S43.Stmt

theorem segLength_nonneg (E : Finset (ℂ × ℂ)) : 0 ≤ segLength E := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem steinerLength_le {P : Finset ℂ} {E : Finset (ℂ × ℂ)} (h : Connects E P) : steinerLength P ≤ segLength E := by
  unfold steinerLength
  apply csInf_le
  · exact ⟨0, by rintro L ⟨E', _, rfl⟩; exact segLength_nonneg E'⟩
  · exact ⟨E, h, rfl⟩

theorem reach_of_mem {E : Finset (ℂ × ℂ)} {u v : ℂ} (h : (u, v) ∈ E) : (segGraph E).Reachable u v := by
  by_cases huv : u = v
  · subst huv; exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    simp only [segGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨(u, v), h, rfl⟩, huv⟩

theorem segLength_insert_le (e : ℂ × ℂ) (S : Finset (ℂ × ℂ)) : segLength (insert e S) ≤ ‖e.1 - e.2‖ + segLength S := by
  unfold segLength
  by_cases he : e ∈ S
  · rw [Finset.insert_eq_of_mem he]; linarith [norm_nonneg (e.1 - e.2)]
  · rw [Finset.sum_insert he]

/-- a set connected to a hub through segments of `E` is connected -/
theorem connects_of_hub {E : Finset (ℂ × ℂ)} {P : Finset ℂ} (hub : ℂ) (h : ∀ p ∈ P, (segGraph E).Reachable hub p) :
    Connects E P := fun a ha b hb => (h a ha).symm.trans (h b hb)

theorem steiner_le_star (a b c x : ℂ) : steinerLength {a, b, c} ≤ starLen a b c x := by
  have hc : Connects {(a, x), (b, x), (c, x)} {a, b, c} := by
    apply connects_of_hub x
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact (reach_of_mem (by simp)).symm
    · exact (reach_of_mem (by simp)).symm
    · exact (reach_of_mem (by simp)).symm
  refine le_trans (steinerLength_le hc) ?_
  unfold starLen dist
  refine le_trans (segLength_insert_le _ _) ?_
  have := segLength_insert_le (b, x) {(c, x)}
  simp only [segLength, Finset.sum_singleton] at this ⊢
  linarith

theorem steiner_le_seg (a b : ℂ) : steinerLength {a, b} ≤ dist a b := by
  have hc : Connects {(a, b)} {a, b} := by
    apply connects_of_hub a
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact reach_of_mem (by simp)
  refine le_trans (steinerLength_le hc) ?_
  simp [segLength, dist]

theorem steiner_le_pair (a b c d x y : ℂ) : steinerLength {a, b, c, d} ≤ pairLen a b c d x y := by
  have hxy : (segGraph {(a, x), (b, x), (x, y), (c, y), (d, y)}).Reachable x y := reach_of_mem (by simp)
  have hc : Connects {(a, x), (b, x), (x, y), (c, y), (d, y)} {a, b, c, d} := by
    apply connects_of_hub x
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact (reach_of_mem (by simp)).symm
    · exact (reach_of_mem (by simp)).symm
    · exact hxy.trans (reach_of_mem (by simp)).symm
    · exact hxy.trans (reach_of_mem (by simp)).symm
  refine le_trans (steinerLength_le hc) ?_
  unfold pairLen dist
  refine le_trans (segLength_insert_le _ _) ?_
  have h2 := segLength_insert_le (b, x) {(x, y), (c, y), (d, y)}
  have h3 := segLength_insert_le (x, y) {(c, y), (d, y)}
  have h4 := segLength_insert_le (c, y) {(d, y)}
  simp only [segLength, Finset.sum_singleton] at h2 h3 h4 ⊢
  linarith

theorem steiner_le_zero (p : Option ℂ) : steinerLength (p.toList.toFinset) ≤ 0 := by
  have hc : Connects ∅ (p.toList.toFinset) := by
    intro a ha b hb
    cases p <;> simp at ha hb
    subst ha; subst hb; exact SimpleGraph.Reachable.refl _
  exact le_trans (steinerLength_le hc) (by simp [segLength])

theorem psiNet_le_psiY2 (w : Vars) (ω : Wit) : psiNet w ω ≤ psiY2 w := by
  unfold psiNet psiY2
  have h1 := steiner_le_star (pts w).A (pts w).B (pts w).D ω.p1
  have h2 := steiner_le_star (pts w).D (pts w).Q ((pts w).Q + ((2 * w.d + w.c - w.f : ℝ) : ℂ)) ω.p2
  simp only at h1 h2 ⊢
  push_cast at h2 ⊢
  linarith

/-! ## Explicit networks for any subset of their terminals -/

theorem segLength_star_le (a b c x : ℂ) : segLength {(a, x), (b, x), (c, x)} ≤ starLen a b c x := by
  unfold starLen dist
  refine le_trans (segLength_insert_le _ _) ?_
  have := segLength_insert_le (b, x) {(c, x)}
  simp only [segLength, Finset.sum_singleton] at this ⊢
  linarith

theorem segLength_pair_le (a b c d x y : ℂ) :
    segLength {(a, x), (b, x), (x, y), (c, y), (d, y)} ≤ pairLen a b c d x y := by
  unfold pairLen dist
  refine le_trans (segLength_insert_le _ _) ?_
  have h2 := segLength_insert_le (b, x) {(x, y), (c, y), (d, y)}
  have h3 := segLength_insert_le (x, y) {(c, y), (d, y)}
  have h4 := segLength_insert_le (c, y) {(d, y)}
  simp only [segLength, Finset.sum_singleton] at h2 h3 h4 ⊢
  linarith

theorem steiner_le_star' {P : Finset ℂ} (a b c x : ℂ) (hP : ∀ p ∈ P, p = a ∨ p = b ∨ p = c) :
    steinerLength P ≤ starLen a b c x := by
  have hc : Connects {(a, x), (b, x), (c, x)} P := by
    apply connects_of_hub x
    intro p hp
    rcases hP p hp with rfl | rfl | rfl <;> exact (reach_of_mem (by simp)).symm
  exact le_trans (steinerLength_le hc) (segLength_star_le a b c x)

theorem steiner_le_seg' {P : Finset ℂ} (a b : ℂ) (hP : ∀ p ∈ P, p = a ∨ p = b) : steinerLength P ≤ dist a b := by
  have hc : Connects {(a, b)} P := by
    apply connects_of_hub a
    intro p hp
    rcases hP p hp with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact reach_of_mem (by simp)
  exact le_trans (steinerLength_le hc) (by simp [segLength, dist])

theorem steiner_le_pair' {P : Finset ℂ} (a b c d x y : ℂ) (hP : ∀ p ∈ P, p = a ∨ p = b ∨ p = c ∨ p = d) :
    steinerLength P ≤ pairLen a b c d x y := by
  have hxy : (segGraph {(a, x), (b, x), (x, y), (c, y), (d, y)}).Reachable x y := reach_of_mem (by simp)
  have hc : Connects {(a, x), (b, x), (x, y), (c, y), (d, y)} P := by
    apply connects_of_hub x
    intro p hp
    rcases hP p hp with rfl | rfl | rfl | rfl
    · exact (reach_of_mem (by simp)).symm
    · exact (reach_of_mem (by simp)).symm
    · exact hxy.trans (reach_of_mem (by simp)).symm
    · exact hxy.trans (reach_of_mem (by simp)).symm
  exact le_trans (steinerLength_le hc) (segLength_pair_le a b c d x y)

theorem steiner_le_zero' {P : Finset ℂ} (a : ℂ) (hP : ∀ p ∈ P, p = a) : steinerLength P ≤ 0 := by
  have hc : Connects ∅ P := by
    intro p hp q hq; rw [hP p hp, hP q hq]
  exact le_trans (steinerLength_le hc) (by simp [segLength])

/-! ## Node ids, lemma availability -/

theorem nodePt_of_lt {F : Fam} {id : ℕ} (h : id < nn F) (w : Vars) : nodePt F w id = some (pt F w id) := by
  unfold pt
  cases F <;> simp only [nn] at h <;> interval_cases id <;> simp [nodePt]

theorem mem_sPlus {F : Fam} {sp : S43.Split} (hall : ∀ id ∈ sp.sp.toList, id < nn F) (w : Vars) (p : ℂ)
    (hp : p ∈ (sp.sp.toList.filterMap (nodePt F w)).toFinset) : ∃ id ∈ sp.sp.toList, p = pt F w id := by
  simp only [List.mem_toFinset, List.mem_filterMap] at hp
  obtain ⟨id, hid, he⟩ := hp
  rw [nodePt_of_lt (hall id hid) w] at he
  exact ⟨id, hid, (Option.some_inj.mp he).symm⟩

theorem avail_some (F : Fam) (L : ℕ) (K : Key) (w : Vars) (h : avail F L K = true) :
    ∃ cb, lemmaBound F L K w = some cb := by
  cases K <;> cases F <;> simp only [avail, decide_eq_true_eq, Bool.decide_and, Bool.and_eq_true] at h <;>
    (try rcases h with h | h | h | h | h) <;> (try obtain ⟨h1, h2⟩ := h) <;> subst_vars <;> simp [lemmaBound] <;> simp_all

/-! ## The bridge -/

/-- the condition a term carries in the statement -/
def condK (F : Fam) (L : ℕ) (w : Vars) : TermK → Prop
  | .seg _ _ => True
  | .bnd K => (lemmaBound F L K w).elim False (·.1)

theorem tEdge_of_tKind {F : Fam} {L : ℕ} {a b : ℕ} {k : TermK} (h : tKind F L a b = some k) (w : Vars) :
    tEdge F L w a b = some (condK F L w k, kVal F L w k) := by
  unfold tKind at h
  unfold tEdge
  dsimp only at h ⊢
  by_cases hxy : a = (ids F).nX ∨ b = (ids F).nX ∨ a = (ids F).nY ∨ b = (ids F).nY
  · rw [if_pos hxy] at h ⊢
    cases hK : edgeKey F a b with
    | none => rw [hK] at h; simp at h
    | some K =>
      rw [hK] at h
      simp only [Option.bind] at h ⊢
      by_cases hav : avail F L K = true
      · rw [if_pos hav] at h
        cases h
        obtain ⟨cb, hcb⟩ := avail_some F L K w hav
        simp [hcb, condK, kVal]
      · rw [if_neg hav] at h; cases h
  · rw [if_neg hxy] at h ⊢
    by_cases hr : a < nn F ∧ b < nn F
    · rw [if_pos hr] at h
      cases h
      simp only [nodePt_of_lt hr.1 w, nodePt_of_lt hr.2 w, condK, kVal]
    · rw [if_neg hr] at h; cases h

theorem mapM_zipWith {α β γ δ : Type} (f : α → β → Option γ) (g : α → β → Option δ) (h : γ → δ)
    (hfg : ∀ a b k, f a b = some k → g a b = some (h k)) :
    ∀ (xs : List α) (ys : List β) (ks : List γ),
      (List.zipWith f xs ys).mapM id = some ks → (List.zipWith g xs ys).mapM id = some (ks.map h) := by
  intro xs
  induction xs with
  | nil => intro ys ks hk; simp at hk; subst hk; simp
  | cons x xs ih =>
    intro ys ks hk
    cases ys with
    | nil => simp at hk; subst hk; simp
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mapM_cons, id] at hk ⊢
      cases hf : f x y with
      | none => simp [hf] at hk
      | some k =>
        cases hr : (List.zipWith f xs ys).mapM id with
        | none => simp [hf, hr] at hk
        | some ks' =>
          simp [hf, hr] at hk
          subst hk
          simp [hfg x y k hf, ih ys ks' hr]

theorem sPlus_le {F : Fam} {L : ℕ} {sp : S43.Split} {sk : SPK} (hsk : spKind F L sp = some sk) (w : Vars) (ω : Wit) :
    sPlus F sp w ≤ spVal F w ω sk := by
  unfold spKind at hsk
  dsimp only at hsk
  by_cases hall0 : (sp.sp.toList.all (· < nn F)) = true
  swap
  · rw [if_pos (by simp [hall0])] at hsk; cases hsk
  rw [if_neg (by simp [hall0])] at hsk
  have hall' : ∀ id ∈ sp.sp.toList, id < nn F := by
    intro id hid; have := List.all_eq_true.mp hall0 id hid; simpa using this
  have mem := mem_sPlus hall' w
  unfold sPlus
  generalize hl : sp.sp.toList = l at hsk mem hall'
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · cases hsk; exact steiner_le_zero' 0 (fun p hp => by obtain ⟨id, hid, _⟩ := mem p hp; simp at hid)
  · cases hsk; exact steiner_le_zero' (pt F w a) (fun p hp => by obtain ⟨id, hid, rfl⟩ := mem p hp; simp at hid; rw [hid])
  · cases hsk
    exact steiner_le_seg' _ _ (fun p hp => by
      obtain ⟨id, hid, rfl⟩ := mem p hp; simp at hid; rcases hid with rfl | rfl <;> simp)
  · cases hsk
    exact steiner_le_star' _ _ _ _ (fun p hp => by
      obtain ⟨id, hid, rfl⟩ := mem p hp; simp at hid; rcases hid with rfl | rfl | rfl <;> simp)
  · -- four points: the pairing is a reordering of the sorted S+ list
    simp only at hsk
    have key : ∀ (l4 : List ℕ) (i j k m : ℕ), [a, b, c, d] = S43.sorted4 l4 → (∀ x ∈ l4, x = i ∨ x = j ∨ x = k ∨ x = m) →
        ∀ p ∈ ((([a, b, c, d] : List ℕ).filterMap (nodePt F w)).toFinset),
          p = pt F w i ∨ p = pt F w j ∨ p = pt F w k ∨ p = pt F w m := by
      intro l4 i j k m hs hl4 p hp
      obtain ⟨id, hid, rfl⟩ := mem p hp
      rw [hs] at hid
      have := hl4 id (by simpa [S43.sorted4, List.mem_mergeSort] using hid)
      rcases this with rfl | rfl | rfl | rfl <;> simp
    by_cases h1 : [a, b, c, d] = S43.sorted4 [(ids F).nA, (ids F).nD, (ids F).nQ, (ids F).nR]
    · rw [if_pos h1] at hsk
      by_cases h3 : L = 3
      · rw [if_pos h3] at hsk; cases hsk
        exact steiner_le_pair' _ _ _ _ _ _ (key _ _ _ _ _ h1 (by intro x hx; simp at hx; tauto))
      · rw [if_neg h3] at hsk
        by_cases h47 : L = 4 ∨ L = 7
        · rw [if_pos h47] at hsk; cases hsk
          exact steiner_le_pair' _ _ _ _ _ _ (key _ _ _ _ _ h1 (by intro x hx; simp at hx; tauto))
        · rw [if_neg h47] at hsk; cases hsk
    · rw [if_neg h1] at hsk
      by_cases h2 : [a, b, c, d] = S43.sorted4 [(ids F).nB, (ids F).nD, (ids F).nQ, (ids F).nR]
      · rw [if_pos h2] at hsk
        by_cases h6 : L = 6
        · rw [if_pos h6] at hsk; cases hsk
          exact steiner_le_pair' _ _ _ _ _ _ (key _ _ _ _ _ h2 (by intro x hx; simp at hx; tauto))
        · rw [if_neg h6] at hsk; cases hsk
      · rw [if_neg h2] at hsk; cases hsk
  · cases hsk

/-- **bridge**: the network property plus the subcase conditions give the statement's `certifies` -/
theorem bridge {F : Fam} {fval L : ℕ} {sp : S43.Split} {ρ : ℝ} {ks : List TermK} {sk : SPK} {w : Vars} {ω : Wit}
    (hks : tKinds F L sp = some ks) (hsk : spKind F L sp = some sk)
    (hv : vset F fval L sp ρ ks sk w ω) (hs : ∀ k ∈ ks, kScond F fval w k) : certifies F sp L ρ w := by
  obtain ⟨_, hc, hg⟩ := hv
  refine ⟨ks.map (fun k => (condK F L w k, kVal F L w k)), ?_, ?_, ?_⟩
  · exact mapM_zipWith (tKind F L) (tEdge F L w) _ (fun a b k h => tEdge_of_tKind h w) _ _ ks hks
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨k, hk, rfl⟩ := he
    have h1 := hc k hk; have h2 := hs k hk
    cases k with
    | seg a b => trivial
    | bnd K =>
      cases K with
      | Y =>
        simp only [condK, kVcond, kScond] at h1 h2 ⊢
        cases F
        · simp only [lemmaBound, Option.elim]
          by_cases hf : fval = 3
          · right; exact lt_of_lt_of_le (h1 ⟨rfl, hf⟩) (psiNet_le_psiY2 w ω)
          · left; exact h2 (fun h => hf h.2)
        · simp only [lemmaBound, Option.elim]; exact h2 (fun h => by cases h.1)
      | _ => exact h1
  · have hsp := sPlus_le hsk w ω
    simp only [List.map_map]
    unfold gNet at hg
    have : (ks.map (Prod.snd ∘ fun k => (condK F L w k, kVal F L w k))) = ks.map (kVal F L w) := by
      simp [Function.comp]
    rw [this]; linarith

end S43.Stmt
