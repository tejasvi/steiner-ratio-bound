module

public import S43.Sound.EvalSound
public import S43.Sound.Unbounded
public import S43Core.Tree

@[expose] public section

/-! # Soundness of the record check

A record box (mantissas at scale `2^-P`, upper ends possibly infinite) is read as the real box `InBox`. If
`checkRecord` accepts it, every point of the box has the network property (`checkRecord_ok`): the vertices of its
finite face by `evalVertexN_sound`, the finite face by convexity (`vset_box`), the infinite sides by the monotonicity
steps (`vset_unbounded`). A skip verdict means the box misses the case domain or the subcase. -/

namespace S43

attribute [local irreducible] P

open DI

/-! ## Arrays -/

theorem get_set! {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) (hi : i < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.set! i v) j (by simpa [Array.set!] using hj), getElem!_pos a j hj]
    simp [Array.set!, Array.getElem_setIfInBounds hj]
  · rw [getElem!_neg (a.set! i v) j (by simpa [Array.set!] using hj), getElem!_neg a j hj]
    by_cases e : i = j
    · subst e; omega
    · simp [e]

theorem set!_of_ge {α : Type} (a : Array α) (i : ℕ) (v : α) (hi : ¬ i < a.size) : a.set! i v = a := by
  simp [Array.set!, Array.setIfInBounds, hi]

theorem size_set! {α : Type} (a : Array α) (i : ℕ) (v : α) : (a.set! i v).size = a.size := by
  simp [Array.set!]

/-! ## The four cases -/

def caseOf (F : Stmt.Fam) (fval : ℕ) : Case := mkCase (decide (F = .st)) fval

theorem caseOf_I (F : Stmt.Fam) (fval : ℕ) : (caseOf F fval).I = Stmt.ids F := by cases F <;> rfl
theorem caseOf_fval (F : Stmt.Fam) (fval : ℕ) : (caseOf F fval).fval = fval := rfl
theorem caseOf_splits (F : Stmt.Fam) (fval : ℕ) : (caseOf F fval).splits = Stmt.splits F := by cases F <;> rfl
theorem caseOf_nb (F : Stmt.Fam) (fval : ℕ) : (caseOf F fval).nb = Stmt.nbOf F fval := by
  cases F <;> by_cases h : fval = 2 <;> simp [caseOf, mkCase, Stmt.nbOf, h, idsSt, idsReg]

/-! ## Real boxes -/

noncomputable def loR (bx : Box) (j : ℕ) : ℝ := (bx.lo[j]! : ℝ) / 2 ^ P
noncomputable def hiR (bx : Box) (j : ℕ) : Option ℝ := (bx.hi[j]!).map fun h => (h : ℝ) / 2 ^ P

/-- `x` lies in the (possibly unbounded) box -/
def InBox (bx : Box) {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ j : Fin n, loR bx j ≤ x j ∧ ∀ h, hiR bx j = some h → x j ≤ h

/-! ## Variable values at a vertex -/

theorem varOf_embed {F : Stmt.Fam} {fval : ℕ} (x : Fin (Stmt.nbOf F fval) → ℝ) (j : ℕ) (hj : j < Stmt.nbOf F fval) :
    Stmt.varOf F (Stmt.embed F fval x) j = x ⟨j, hj⟩ := by
  cases F <;> by_cases h2 : fval = 2 <;> simp only [Stmt.nbOf, h2, ite_true, ite_false] at hj <;>
    interval_cases j <;> simp [Stmt.varOf, Stmt.embed, h2, Stmt.nbOf]

theorem varOf_embed_f (x : Fin (Stmt.nbOf .st 2) → ℝ) :
    Stmt.varOf .st (Stmt.embed .st 2 x) 7 = x ⟨2, by simp [Stmt.nbOf]⟩ := by
  simp [Stmt.varOf, Stmt.embed, Stmt.nbOf]

theorem varOf_ge (F : Stmt.Fam) (w : Stmt.Vars) (j : ℕ) (hj : (Stmt.ids F).NV ≤ j) : Stmt.varOf F w j = 0 := by
  have h8 : ∀ (l : List ℝ), l.length ≤ j → l.getD j 0 = 0 := fun l hl => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl]
  cases F <;> simp [Stmt.ids, idsSt, idsReg] at hj <;> unfold Stmt.varOf <;> exact h8 _ (by simp; omega)

theorem default_DI : (default : DI) = ⟨0, 0⟩ := rfl

theorem vertexV_enc {F : Stmt.Fam} {fval : ℕ} (hf2 : fval = 2 → F = .st) (ch : ℕ → ℤ)
    (x : Fin (Stmt.nbOf F fval) → ℝ) (hx : ∀ j : Fin (Stmt.nbOf F fval), x j = (ch j : ℝ) / 2 ^ P) :
    VEnc F (vertexV (caseOf F fval) ch) (Stmt.embed F fval x) := by
  intro j
  have hsize : (vertexV (caseOf F fval) ch).size = (Stmt.ids F).NV := by simp [vertexV, caseOf_I]
  by_cases hj : j < (Stmt.ids F).NV
  · rw [getElem!_pos _ j (by rw [hsize]; exact hj)]
    simp only [vertexV, Array.getElem_ofFn, caseOf_nb, caseOf_fval, caseOf_I]
    by_cases hjn : j < Stmt.nbOf F fval
    · rw [if_pos hjn, varOf_embed x j hjn, hx ⟨j, hjn⟩]; exact enc_ofMant _
    · rw [if_neg hjn]
      -- only f := d (fval 2, d_steiner) has a variable beyond the box coordinates
      by_cases h2 : fval = 2
      · obtain rfl := hf2 h2; subst h2
        have : j = 7 := by simp [Stmt.ids, idsSt, Stmt.nbOf] at hj hjn; omega
        subst this
        simp only [Stmt.ids, idsSt, beq_self_eq_true, Bool.and_self, ite_true]
        rw [varOf_embed_f, hx ⟨2, _⟩]; exact enc_ofMant _
      · exfalso; cases F <;> simp [Stmt.ids, idsSt, idsReg, Stmt.nbOf, h2] at hj hjn <;> omega
  · rw [getElem!_neg _ j (by rw [hsize]; exact hj), varOf_ge F _ j (by omega), default_DI]
    exact ⟨by simp, by simp⟩

/-! ## The vertex loop -/

theorem allVerts_sound (f : (ℕ → ℤ) → Bool) (bx : Box) :
    ∀ k (ch : ℕ → ℤ), allVerts f bx k ch = true → ∀ ch' : ℕ → ℤ,
      (∀ j < k, ch' j = bx.lo[j]! ∨ bx.hi[j]! = some (ch' j)) → (∀ j, k ≤ j → ch' j = ch j) → f ch' = true := by
  intro k
  induction k with
  | zero =>
    intro ch h ch' _ h2
    have : ch' = ch := funext fun j => h2 j (Nat.zero_le _)
    subst this; exact h
  | succ k ih =>
    intro ch h ch' h1 h2
    simp only [allVerts, Bool.and_eq_true] at h
    obtain ⟨hlo, hhi⟩ := h
    rcases h1 k (Nat.lt_succ_self k) with hk | hk
    · refine ih _ hlo ch' (fun j hj => h1 j (by omega)) (fun j hj => ?_)
      by_cases e : j = k
      · subst e; simp [hk]
      · simp [e, h2 j (by omega)]
    · rw [hk] at hhi
      simp only at hhi
      refine ih _ hhi ch' (fun j hj => h1 j (by omega)) (fun j hj => ?_)
      by_cases e : j = k
      · subst e; simp
      · simp [e, h2 j (by omega)]

/-! ## Facts about the published splits (checked by `native_decide` in `S43.Sound.Data`) -/

/-- the monotonicity masks give the monotonicity rule wherever the checker relies on them -/
def MonoData (F : Stmt.Fam) (fval : ℕ) : Prop :=
  ∀ sp ∈ Stmt.splits F, ∀ L ≤ 8, ∀ ks sk, Stmt.tKinds F L sp = some ks → Stmt.spKind F L sp = some sk →
    (fval = 2 → bit sp.mono (Stmt.ids F).vf = true → Stmt.monoRule F L .f sp ks sk = true) ∧
    (L = 0 → ∀ j < Stmt.nbOf F fval, ¬(fval = 3 ∧ j = (Stmt.ids F).vf) → bit sp.mono j = true →
      Stmt.monoRule F 0 (Stmt.vrOf F j) sp ks sk = true) ∧
    (fval = 3 → hasY (Stmt.ids F) sp = false → extOK (Stmt.ids F) sp = true → Stmt.monoRule F L .f sp ks sk = true)

theorem mem_mapM_zipWith {α β γ : Type} (f : α → β → Option γ) :
    ∀ (xs : List α) (ys : List β) (ks : List γ), (List.zipWith f xs ys).mapM id = some ks →
      ∀ k ∈ ks, ∃ a b, (a, b) ∈ List.zip xs ys ∧ f a b = some k := by
  intro xs
  induction xs with
  | nil => intro ys ks h; simp at h; subst h; simp
  | cons x xs ih =>
    intro ys ks h
    cases ys with
    | nil => simp at h; subst h; simp
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mapM_cons, id] at h
      cases hf : f x y with
      | none => simp [hf] at h
      | some z =>
        cases hr : (List.zipWith f xs ys).mapM id with
        | none => simp [hf, hr] at h
        | some ks' =>
          simp [hf, hr] at h
          subst h
          intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact ⟨x, y, by simp, hf⟩
          · obtain ⟨a, b, hab, he⟩ := ih ys ks' hr k hk
            exact ⟨a, b, by simp [hab], he⟩

theorem edgeKey_AX {I : Ids} {a b : ℕ} (h : S43.edgeKey I a b = some .AX) :
    (a = I.nX ∧ b = I.nA) ∨ (a = I.nA ∧ b = I.nX) := by
  unfold S43.edgeKey at h
  simp only at h
  repeat' (split at h)
  all_goals first | (cases h; done) | (simp_all; done) | skip
  all_goals (simp only [Bool.or_eq_true, beq_iff_eq] at *; omega)

theorem edgeKey_Y {I : Ids} {a b : ℕ} (h : S43.edgeKey I a b = some .Y) : a = I.nY ∨ b = I.nY := by
  unfold S43.edgeKey at h
  simp only at h
  repeat' (split at h)
  all_goals first | (cases h; done) | (simp_all; done) | skip
  all_goals (simp only [Bool.or_eq_true, beq_iff_eq] at *; omega)

theorem tKind_bnd {F : Stmt.Fam} {L a b : ℕ} {K : Stmt.Key} (h : Stmt.tKind F L a b = some (.bnd K)) :
    ∃ K0, S43.edgeKey (Stmt.ids F) a b = some K0 ∧ keyMap K0 = some K := by
  unfold Stmt.tKind at h
  simp only at h
  by_cases hxy : a = (Stmt.ids F).nX ∨ b = (Stmt.ids F).nX ∨ a = (Stmt.ids F).nY ∨ b = (Stmt.ids F).nY
  · rw [if_pos hxy, stmt_edgeKey] at h
    cases hk : S43.edgeKey (Stmt.ids F) a b with
    | none => rw [hk] at h; simp at h
    | some K0 =>
      rw [hk] at h
      simp only [Option.bind_some] at h
      refine ⟨K0, rfl, ?_⟩
      cases hm : keyMap K0 with
      | none => rw [hm] at h; simp at h
      | some K1 =>
        rw [hm] at h
        simp only [Option.bind_some] at h
        split_ifs at h
        simp only [Option.some.injEq, Stmt.TermK.bnd.injEq] at h
        rw [h]
  · rw [if_neg hxy] at h; split_ifs at h <;> simp at h

theorem keyMap_AX {K0 : Key} (h : keyMap K0 = some .AX) : K0 = .AX := by cases K0 <;> simp [keyMap] at h ⊢
theorem keyMap_Y {K0 : Key} (h : keyMap K0 = some .Y) : K0 = .Y := by cases K0 <;> simp [keyMap] at h ⊢

theorem hasAX_of_mem {F : Stmt.Fam} {L : ℕ} {sp : Split} {ks : List Stmt.TermK} (h : Stmt.tKinds F L sp = some ks)
    (hk : Stmt.TermK.bnd .AX ∈ ks) : hasAX (Stmt.ids F) sp = true := by
  obtain ⟨a, b, hab, he⟩ := mem_mapM_zipWith _ _ _ _ h _ hk
  obtain ⟨K0, hk0, hm⟩ := tKind_bnd he
  rw [keyMap_AX hm] at hk0
  have := edgeKey_AX hk0
  unfold hasAX
  rw [List.any_eq_true]
  exact ⟨(a, b), hab, by rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp⟩

theorem hasY_of_mem {F : Stmt.Fam} {L : ℕ} {sp : Split} {ks : List Stmt.TermK} (h : Stmt.tKinds F L sp = some ks)
    (hk : Stmt.TermK.bnd .Y ∈ ks) : hasY (Stmt.ids F) sp = true := by
  obtain ⟨a, b, hab, he⟩ := mem_mapM_zipWith _ _ _ _ h _ hk
  obtain ⟨K0, hk0, hm⟩ := tKind_bnd he
  rw [keyMap_Y hm] at hk0
  have := edgeKey_Y hk0
  unfold hasY
  rw [List.any_eq_true]
  exact ⟨(a, b), hab, by rcases this with rfl | rfl <;> simp⟩

/-! ## The static checks -/

theorem sideOK_spec {C : Case} {sp : Split} {L : ℕ} {bx : Box} {j : ℕ} (h : sideOK C sp L bx j = true) :
    0 ≤ bx.lo[j]! ∧ (∀ hh, bx.hi[j]! = some hh → bx.lo[j]! ≤ hh) ∧
    (bx.hi[j]! = none → if C.fval = 3 ∧ j = C.I.vf then hasY C.I sp = false ∧ extOK C.I sp = true
      else bit sp.mono j = true ∧ L = 0) := by
  unfold sideOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  refine ⟨h0, fun hh e => by rw [e] at h1; simpa using h1, fun e => ?_⟩
  rw [e] at h1
  simp only at h1
  by_cases c : C.fval = 3 ∧ j = C.I.vf
  · rw [if_pos (by simp [c.1, c.2])] at h1; rw [if_pos c]; simpa using h1
  · rw [if_neg (by simpa using c)] at h1; rw [if_neg c]; simpa using h1

theorem embed_nonneg {F : Stmt.Fam} {fval : ℕ} (x : Fin (Stmt.nbOf F fval) → ℝ) (hx : ∀ j, 0 ≤ x j) :
    let w := Stmt.embed F fval x
    0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d ∧ 0 ≤ w.s ∧ 0 ≤ w.u ∧ 0 ≤ w.v ∧ 0 ≤ w.e ∧ 0 ≤ w.f := by
  intro w
  have g : ∀ i, 0 ≤ (if h : i < Stmt.nbOf F fval then x ⟨i, h⟩ else 0) := fun i => by split_ifs <;> simp [hx]
  cases F <;> simp only [w, Stmt.embed] <;> refine ⟨g _, g _, g _, g _, ?_, ?_, g _, ?_⟩ <;>
    first | exact g _ | exact hx _ | exact le_refl 0 | (split_ifs <;> first | exact g _ | exact hx _ | exact le_refl _)

theorem vrOf_c {F : Stmt.Fam} {j : ℕ} (h : Stmt.vrOf F j = .c) : j = 1 := by
  cases F <;> rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [Stmt.vrOf] at h ⊢

/-! ## The record theorem -/

theorem checkRecord_ok {F : Stmt.Fam} {fval : ℕ} (hf2 : fval = 2 → F = .st) {rho : DI} {ρ : ℝ}
    (hrho : rho.Enc ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : MonoData F fval) {bx : Box} {sid lid : ℤ}
    (h : checkRecord (caseOf F fval) rho bx sid lid = .ok) :
    ∃ sp ∈ Stmt.splits F, ∃ L ≤ 8, ∃ ks sk, Stmt.tKinds F L sp = some ks ∧ Stmt.spKind F L sp = some sk ∧
      (∀ k ∈ ks, k = .bnd .Y → fval = 1 ∨ (F = .reg ∧ fval = 3)) ∧
      (fval = 2 → Stmt.monoRule F L .f sp ks sk = true) ∧
      ∀ x : Fin (Stmt.nbOf F fval) → ℝ, InBox bx x → ∃ ω, Stmt.vset F fval L sp ρ ks sk (Stmt.embed F fval x) ω := by
  unfold checkRecord at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4 h5
  all_goals try (simp at h; done)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h1
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h4
  have hs1 : 1 ≤ sid := by omega
  have hs2 : sid ≤ ((caseOf F fval).splits.size : ℤ) := by omega
  have hl0 : 0 ≤ lid := by omega
  have hl8 : lid ≤ 8 := by omega
  rw [caseOf_splits] at hs2 h5
  rw [caseOf_nb] at h1
  set sp := (Stmt.splits F)[sid.toNat - 1]! with hsp
  set L := lid.toNat with hL
  have hidx : sid.toNat - 1 < (Stmt.splits F).size := by omega
  have hspm : sp ∈ Stmt.splits F := by
    rw [hsp, getElem!_pos (Stmt.splits F) (sid.toNat - 1) hidx]; exact Array.getElem_mem hidx
  have hL8 : L ≤ 8 := by omega
  simp only [Bool.and_eq_true] at h5
  obtain ⟨hst, hall⟩ := h5
  rw [caseOf_nb, caseOf_I, caseOf_fval] at hall
  unfold staticOK at hst
  simp only [Bool.and_eq_true, caseOf_nb, caseOf_I, caseOf_fval] at hst
  obtain ⟨⟨⟨hFV2, hside⟩, hY3⟩, hAX⟩ := hst
  have hFV2' : fval = 2 → bit sp.mono (Stmt.ids F).vf = true := fun e => by simpa [e] using hFV2
  have hY3' : fval = 3 → hasY (Stmt.ids F) sp = true → ∀ i < Stmt.nbOf F fval, bx.hi[i]! ≠ none := by
    intro e hy i hi hn
    subst e
    simp [hy] at hY3
    exact hY3 i hi hn
  have hAX' : hasAX (Stmt.ids F) sp = true → bx.hi[(Stmt.ids F).vc]! ≠ none := by
    intro ha hn; simp [ha, hn] at hAX
  have hside' : ∀ j < Stmt.nbOf F fval, _ := fun j hj => sideOK_spec (List.all_eq_true.mp hside j (List.mem_range.mpr hj))
  simp only [caseOf_fval, caseOf_I] at hside'
  have hloR : ∀ j : Fin (Stmt.nbOf F fval), 0 ≤ loR bx j := fun j => by
    have := (hside' j j.isLt).1
    unfold loR; have hp := pow_P_pos; positivity
  have hloHi : ∀ j : Fin (Stmt.nbOf F fval), ∀ hh, hiR bx j = some hh → loR bx j ≤ hh := fun j hh e => by
    unfold hiR at e
    cases e' : bx.hi[(j : ℕ)]! with
    | none => rw [e'] at e; simp at e
    | some h0 =>
      rw [e'] at e; simp at e; subst e
      have := (hside' j j.isLt).2.1 h0 e'
      unfold loR; have hp := pow_P_pos
      exact div_le_div_of_nonneg_right (by exact_mod_cast this) hp.le
  -- every vertex of the finite face is accepted
  let f := fun ch => evalVertexN (Stmt.ids F) fval rho (vertexV (caseOf F fval) ch) sp L
  have hvx : ∀ x : Fin (Stmt.nbOf F fval) → ℝ, (∀ i, x i = loR bx i ∨ x i = (hiR bx i).getD (loR bx i)) →
      ∃ ch : ℕ → ℤ, f ch = true ∧ ∀ j : Fin (Stmt.nbOf F fval), x j = (ch j : ℝ) / 2 ^ P := by
    intro x hx
    classical
    let ch : ℕ → ℤ := fun j => if hj : j < Stmt.nbOf F fval then
      (if x ⟨j, hj⟩ = loR bx j then bx.lo[j]! else (bx.hi[j]!).getD bx.lo[j]!) else 0
    refine ⟨ch, allVerts_sound f bx _ _ hall ch (fun j hj => ?_) (fun j hj => ?_), fun j => ?_⟩
    · simp only [ch, dif_pos hj]
      split_ifs with e
      · left; rfl
      · right
        rcases hx ⟨j, hj⟩ with e' | e'
        · exact absurd e' e
        · cases hh : bx.hi[j]! with
          | none => simp [hiR, hh] at e'; exact absurd e' e
          | some h0 => simp
    · simp only [ch, dif_neg (by omega : ¬ j < Stmt.nbOf F fval)]
    · simp only [ch, dif_pos j.isLt]
      split_ifs with e
      · rw [e]; rfl
      · rcases hx j with e' | e'
        · exact absurd e' e
        · cases hh : bx.hi[(j : ℕ)]! with
          | none => simp [hiR, hh] at e'; exact absurd e' e
          | some h0 => simp [hiR, hh] at e'; simpa using e'
  have hxnn : ∀ x : Fin (Stmt.nbOf F fval) → ℝ, (∀ i, x i = loR bx i ∨ x i = (hiR bx i).getD (loR bx i)) →
      ∀ j, 0 ≤ x j := fun x hx j => by
    rcases hx j with e | e
    · rw [e]; exact hloR j
    · rw [e]
      cases hh : hiR bx j with
      | none => simpa using hloR j
      | some h0 => simpa using le_trans (hloR j) (hloHi j h0 hh)
  -- the term kinds, from the lowest vertex
  obtain ⟨ch0, hf0, hx0⟩ := hvx (fun j => loR bx j) (fun i => Or.inl rfl)
  obtain ⟨ks, sk, hks, hsk, hYk, -⟩ := evalVertexN_sound hrho (vertexV_enc hf2 ch0 _ hx0)
    (embed_nonneg _ (hxnn _ (fun i => Or.inl rfl))) hf0
  have hvert : ∀ x : Fin (Stmt.nbOf F fval) → ℝ, (∀ i, x i = loR bx i ∨ x i = (hiR bx i).getD (loR bx i)) →
      ∃ ω, Stmt.vset F fval L sp ρ ks sk (Stmt.embed F fval x) ω := by
    intro x hx
    obtain ⟨ch, hf, hxc⟩ := hvx x hx
    obtain ⟨ks', sk', hks', hsk', -, hv⟩ := evalVertexN_sound hrho (vertexV_enc hf2 ch _ hxc)
      (embed_nonneg _ (hxnn x hx)) hf
    rw [hks] at hks'; rw [hsk] at hsk'
    cases hks'; cases hsk'
    exact hv
  have hface := Stmt.vset_box hρ0 (fun j => loR bx j) (fun j => (hiR bx j).getD (loR bx j)) hvert
  have hmono' := hmono sp hspm L hL8 ks sk hks hsk
  have hf2mono : fval = 2 → Stmt.monoRule F L .f sp ks sk = true := fun e => hmono'.1 e (hFV2' e)
  refine ⟨sp, hspm, L, hL8, ks, sk, hks, hsk, hYk, hf2mono, ?_⟩
  refine Stmt.vset_unbounded hρ0 hρ1 (fun j => loR bx j) (fun j => hiR bx j) hface (fun j hj => ?_)
  -- an infinite side: the step conditions
  have hnone : bx.hi[(j : ℕ)]! = none := by
    unfold hiR at hj; cases e : bx.hi[(j : ℕ)]! with
    | none => rfl
    | some _ => rw [e] at hj; simp at hj
  have hsj := (hside' j j.isLt).2.2 hnone
  have hvf : Stmt.vrOf F (Stmt.ids F).vf = .f := by cases F <;> rfl
  refine ⟨?_, ?_, fun hc hk => ?_, fun hr hk => ?_, fun e => hf2mono e.1⟩
  · split_ifs at hsj with c
    · right; rw [c.2, hvf]
    · left; exact hsj.2
  · split_ifs at hsj with c
    · rw [c.2, hvf]; exact hmono'.2.2 c.1 hsj.1 hsj.2
    · rw [hsj.2]; exact hmono'.2.1 hsj.2 j j.isLt c hsj.1
  · -- the c side: no A-X edge
    have hj1 : (j : ℕ) = (Stmt.ids F).vc := by
      have := vrOf_c hc; cases F <;> simpa [Stmt.ids, idsSt, idsReg] using this
    exact hAX' (hasAX_of_mem hks hk) (hj1 ▸ hnone)
  · exact hY3' hr.2 (hasY_of_mem hks hk) j j.isLt hnone

end S43

end
