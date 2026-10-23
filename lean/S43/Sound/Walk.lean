import S43.Sound.Target

/-! # Soundness of the tree walks

Halving a box covers it by the two halves, so every point of a walked box lies in a leaf box (`walk_sound`); the
skeleton's job boxes cover `[0, inf)^nb` (`skelBoxes_cover`); a shard covers its jobs (`shardOK_sound`); shards whose job
ranges tile `[0, N)` cover the whole case (`case_of_shards`). -/

namespace S43

attribute [local irreducible] P

/-! ## Halving -/

theorem split_cover (bx : Box) (k : ℕ) (m : ℤ) (hk : k < bx.lo.size) {n : ℕ} (x : Fin n → ℝ) (hx : InBox bx x) :
    InBox ⟨bx.lo, bx.hi.set! k (some m)⟩ x ∨ InBox ⟨bx.lo.set! k m, bx.hi⟩ x := by
  by_cases hc : ∃ hkn : k < n, (m : ℝ) / 2 ^ P < x ⟨k, hkn⟩
  · right
    obtain ⟨hkn, hlt⟩ := hc
    intro j
    refine ⟨?_, fun hh e => (hx j).2 hh (by simpa [hiR] using e)⟩
    unfold loR
    simp only
    rw [get_set! _ _ _ _ hk]
    split_ifs with e
    · have : j = ⟨k, hkn⟩ := Fin.ext e.symm
      subst this; exact hlt.le
    · exact (hx j).1
  · left
    push_neg at hc
    intro j
    refine ⟨(hx j).1, fun hh e => ?_⟩
    unfold hiR at e
    simp only at e
    by_cases hkh : k < bx.hi.size
    · rw [get_set! _ _ _ _ hkh] at e
      split_ifs at e with ejk
      · simp at e
        subst e
        have : j = ⟨k, ejk ▸ j.isLt⟩ := Fin.ext ejk.symm
        rw [this]; exact hc _
      · exact (hx j).2 hh (by simpa [hiR] using e)
    · rw [set!_of_ge _ _ _ hkh] at e; exact (hx j).2 hh (by simpa [hiR] using e)

theorem halves_cover {bx l r : Box} {k : ℕ} (h : halves bx k = some (l, r)) {n : ℕ} (x : Fin n → ℝ) (hx : InBox bx x) :
    InBox l x ∨ InBox r x := by
  unfold halves at h
  split_ifs at h with hk
  simp only at h
  have hk' : k < bx.lo.size := by omega
  cases e : bx.hi[k]! with
  | none =>
    rw [e] at h; simp only at h
    split_ifs at h
    all_goals try (simp at h; done)
    all_goals (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact split_cover bx k _ hk' x hx)
  | some hh =>
    rw [e] at h; simp only at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact split_cover bx k _ hk' x hx

/-! ## Walks -/

theorem walk_sound {C : Case} {rho : DI} {cs : Codes} {G : (Fin C.nb → ℝ) → Prop}
    (hleaf : ∀ bx sid lid, checkRecord C rho bx sid lid ≠ .fail → ∀ x, InBox bx x → G x) :
    ∀ fuel i bx i', walk C rho cs fuel i bx = some i' → ∀ x, InBox bx x → G x := by
  intro fuel
  induction fuel with
  | zero => intro i bx i' h; simp [walk] at h
  | succ fuel ih =>
    intro i bx i' h x hx
    unfold walk at h
    simp only at h
    split_ifs at h with h1 h2
    all_goals try (simp at h; done)
    · cases hh : halves bx (cs.get i - 33) with
      | none => rw [hh] at h; simp at h
      | some lr =>
        obtain ⟨l, r⟩ := lr
        rw [hh] at h; simp only at h
        cases h1' : walk C rho cs fuel (i + 1) l with
        | none => rw [h1'] at h; simp at h
        | some i1 =>
          rw [h1'] at h; simp only at h
          rcases halves_cover hh x hx with hl | hr
          · exact ih _ _ _ h1' x hl
          · exact ih _ _ _ h x hr
    · cases hl : leafAt cs i with
      | none => rw [hl] at h; simp at h
      | some p =>
        obtain ⟨lid, sid⟩ := p
        rw [hl] at h; simp only at h
        split_ifs at h with hc
        exact hleaf bx sid lid (by simpa using hc) x hx

theorem walkSkel_cover {C : Case} {cs : Codes} : ∀ fuel i bx i' bs, walkSkel C cs fuel i bx = some (i', bs) →
    ∀ {n : ℕ} (x : Fin n → ℝ), InBox bx x → ∃ b ∈ bs, InBox b x := by
  intro fuel
  induction fuel with
  | zero => intro i bx i' bs h; simp [walkSkel] at h
  | succ fuel ih =>
    intro i bx i' bs h n x hx
    unfold walkSkel at h
    simp only at h
    split_ifs at h with h1 h2 h3
    all_goals try (simp at h; done)
    · cases hh : halves bx (cs.get i - 33) with
      | none => rw [hh] at h; simp at h
      | some lr =>
        obtain ⟨l, r⟩ := lr
        rw [hh] at h; simp only at h
        cases e1 : walkSkel C cs fuel (i + 1) l with
        | none => rw [e1] at h; simp at h
        | some p1 =>
          obtain ⟨i1, b1⟩ := p1
          rw [e1] at h; simp only at h
          cases e2 : walkSkel C cs fuel i1 r with
          | none => rw [e2] at h; simp at h
          | some p2 =>
            obtain ⟨i2, b2⟩ := p2
            rw [e2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            rcases halves_cover hh x hx with hl | hr
            · obtain ⟨b, hb, hbx⟩ := ih _ _ _ _ e1 x hl; exact ⟨b, List.mem_append_left _ hb, hbx⟩
            · obtain ⟨b, hb, hbx⟩ := ih _ _ _ _ e2 x hr; exact ⟨b, List.mem_append_right _ hb, hbx⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨bx, List.mem_singleton_self _, hx⟩

theorem walkTopSkel_cover {C : Case} {cs : Codes} {fuel : ℕ} : ∀ k i bx i' bs,
    walkTopSkel C cs fuel k i bx = some (i', bs) → ∀ {n : ℕ} (x : Fin n → ℝ), InBox bx x → ∃ b ∈ bs, InBox b x := by
  intro k
  induction k with
  | zero => intro i bx i' bs h n x hx; exact walkSkel_cover _ _ _ _ _ h x hx
  | succ k ih =>
    intro i bx i' bs h n x hx
    unfold walkTopSkel at h
    cases hh : halves bx k with
    | none => rw [hh] at h; simp at h
    | some lr =>
      obtain ⟨l, r⟩ := lr
      rw [hh] at h; simp only at h
      cases e1 : walkTopSkel C cs fuel k i l with
      | none => rw [e1] at h; simp at h
      | some p1 =>
        obtain ⟨i1, b1⟩ := p1
        rw [e1] at h; simp only at h
        cases e2 : walkTopSkel C cs fuel k i1 r with
        | none => rw [e2] at h; simp at h
        | some p2 =>
          obtain ⟨i2, b2⟩ := p2
          rw [e2] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          rcases halves_cover hh x hx with hl | hr
          · obtain ⟨b, hb, hbx⟩ := ih _ _ _ _ e1 x hl; exact ⟨b, List.mem_append_left _ hb, hbx⟩
          · obtain ⟨b, hb, hbx⟩ := ih _ _ _ _ e2 x hr; exact ⟨b, List.mem_append_right _ hb, hbx⟩

theorem inBox_top (nb : ℕ) {n : ℕ} (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) : InBox (topBox nb) x := by
  intro j
  refine ⟨?_, fun hh e => ?_⟩
  · unfold loR topBox
    by_cases hj : (j : ℕ) < nb
    · rw [getElem!_pos _ _ (by simpa using hj)]; simpa using hx j
    · rw [getElem!_neg _ _ (by simpa using hj)]; simpa using hx j
  · unfold hiR topBox at e
    by_cases hj : (j : ℕ) < nb
    · rw [getElem!_pos _ _ (by simpa using hj)] at e; simp at e
    · rw [getElem!_neg _ _ (by simpa using hj)] at e
      have : (default : Option ℤ) = none := rfl
      rw [this] at e; simp at e

theorem skelBoxes_cover {C : Case} {cs : Codes} {bs : Array Box} (h : skelBoxes C cs = some bs) {n : ℕ}
    (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) : ∃ j < bs.size, InBox bs[j]! x := by
  unfold skelBoxes at h
  cases e : walkTopSkel C cs 200 C.nb 0 (topBox C.nb) with
  | none => rw [e] at h; simp at h
  | some p =>
    obtain ⟨i, l⟩ := p
    rw [e] at h; simp only at h
    split_ifs at h
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨b, hb, hbx⟩ := walkTopSkel_cover _ _ _ _ _ e x (inBox_top C.nb x hx)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    refine ⟨j, by simpa using hj, ?_⟩
    rw [getElem!_pos _ _ (by simpa using hj)]; simpa using hbx

/-! ## Shards -/

theorem jobsOK_sound {C : Case} {rho : DI} {cs : Codes} {bs : Array Box} {G : (Fin C.nb → ℝ) → Prop}
    (hleaf : ∀ bx sid lid, checkRecord C rho bx sid lid ≠ .fail → ∀ x, InBox bx x → G x) :
    ∀ n j i, jobsOK C rho cs bs n j i = true → ∀ k < n, ∀ x, InBox bs[j + k]! x → G x := by
  intro n
  induction n with
  | zero => intro j i _ k hk; omega
  | succ n ih =>
    intro j i h k hk x hx
    unfold jobsOK at h
    cases e : walk C rho cs 200 i bs[j]! with
    | none => rw [e] at h; simp at h
    | some i' =>
      rw [e] at h; simp only at h
      rcases k with _ | k
      · exact walk_sound hleaf _ _ _ _ e x (by simpa using hx)
      · exact ih (j + 1) i' h k (by omega) x (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hx)

theorem shardOK_sound {C : Case} {rho : DI} {skel cs : Codes} {j0 n : ℕ} {G : (Fin C.nb → ℝ) → Prop}
    (hleaf : ∀ bx sid lid, checkRecord C rho bx sid lid ≠ .fail → ∀ x, InBox bx x → G x)
    (h : shardOK C rho skel cs j0 n = true) :
    ∃ bs, skelBoxes C skel = some bs ∧ ∀ k < n, ∀ x, InBox bs[j0 + k]! x → G x := by
  unfold shardOK at h
  cases e : skelBoxes C skel with
  | none => rw [e] at h; simp at h
  | some bs =>
    rw [e] at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨bs, rfl, jobsOK_sound hleaf n j0 0 h.2⟩

theorem shardOKPar_sound {C : Case} {rho : DI} {skel cs : Codes} {j0 n : ℕ} {G : (Fin C.nb → ℝ) → Prop}
    (hleaf : ∀ bx sid lid, checkRecord C rho bx sid lid ≠ .fail → ∀ x, InBox bx x → G x)
    (h : shardOKPar C rho skel cs j0 n = true) :
    ∃ bs, skelBoxes C skel = some bs ∧ ∀ k < n, ∀ x, InBox bs[j0 + k]! x → G x := by
  unfold shardOKPar at h
  cases e1 : skelBoxes C skel with
  | none => rw [e1] at h; simp at h
  | some bs =>
    cases e2 : jobStarts C cs n 0 with
    | none => rw [e1, e2] at h; simp at h
    | some starts =>
      rw [e1, e2] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_map] at h
      obtain ⟨⟨-, hlen⟩, hall⟩ := h
      refine ⟨bs, rfl, fun k hk x hx => ?_⟩
      have hk' : k < starts.length := by omega
      have hmem : (starts[k], k) ∈ starts.zip (List.range n) := by
        rw [List.mem_iff_getElem]
        exact ⟨k, by simp; omega, by simp⟩
      have ht := hall _ ⟨_, hmem, rfl⟩
      change (walk C rho cs 200 starts[k] bs[j0 + k]!).isSome = true at ht
      cases e : walk C rho cs 200 starts[k] bs[j0 + k]! with
      | none => rw [e] at ht; simp at ht
      | some i' => exact walk_sound hleaf _ _ _ _ e x hx

/-- consecutive job ranges `(j0, n)` starting at `j` and ending at `N` -/
def contig : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], j, N => j == N
  | (a, n) :: rs, j, N => a == j && contig rs (j + n) N

theorem contig_cover : ∀ (rs : List (ℕ × ℕ)) (j N : ℕ), contig rs j N = true →
    ∀ t, j ≤ t → t < N → ∃ r ∈ rs, r.1 ≤ t ∧ t < r.1 + r.2 := by
  intro rs
  induction rs with
  | nil => intro j N h t h1 h2; simp [contig] at h; omega
  | cons r rs ih =>
    intro j N h t h1 h2
    obtain ⟨a, n⟩ := r
    simp only [contig, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    by_cases ht : t < a + n
    · exact ⟨(a, n), List.mem_cons_self, h1, ht⟩
    · obtain ⟨r', hr', h'⟩ := ih _ _ h t (by omega) h2
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

/-- a case from its skeleton and shards: every point of `[0, inf)^nb` satisfies `G` -/
theorem case_of_shards {C : Case} {rho : DI} {skel : Codes} {G : (Fin C.nb → ℝ) → Prop}
    (hleaf : ∀ bx sid lid, checkRecord C rho bx sid lid ≠ .fail → ∀ x, InBox bx x → G x)
    (ranges : List (ℕ × ℕ)) (hcont : contig ranges 0 (skelSize C skel) = true)
    (hshard : ∀ r ∈ ranges, ∃ cs, shardOKPar C rho skel cs r.1 r.2 = true)
    (hsome : (skelBoxes C skel).isSome = true) :
    ∀ x : Fin C.nb → ℝ, (∀ j, 0 ≤ x j) → G x := by
  intro x hx
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨j, hj, hjx⟩ := skelBoxes_cover hbs x hx
  have hN : skelSize C skel = bs.size := by simp [skelSize, hbs]
  obtain ⟨r, hr, hr1, hr2⟩ := contig_cover ranges 0 _ hcont j (Nat.zero_le _) (by omega)
  obtain ⟨cs, hcs⟩ := hshard r hr
  obtain ⟨bs', hbs', hall⟩ := shardOKPar_sound hleaf hcs
  rw [hbs] at hbs'; cases hbs'
  exact hall (j - r.1) (by omega) x (by rw [show r.1 + (j - r.1) = j by omega]; exact hjx)

end S43
