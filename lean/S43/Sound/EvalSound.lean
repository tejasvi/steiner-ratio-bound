import S43.Sound.LemmaSound

/-! # Soundness of `evalVertexN`

The witness `ω` of a vertex: the Steiner points the checker used for the S+ network (`spWit`) and for Lemma Y2's two
SMT terms (`psiWit`), as exact dyadic points. -/

namespace S43

attribute [local irreducible] P

open DI

/-! ## Lemma Y2 -/

/-- the two Steiner points of Psi's explicit networks -/
noncomputable def psiWit (V : Array DI) (P : Array Pt) (w : Stmt.Vars) : ℂ × ℂ :=
  let I := idsReg; let p := Stmt.pts w
  let Q := P[I.nQ]!
  let Qs : Pt := (Q.1 + ((V[I.vd]!).nmul 2 + V[I.vc]! - V[I.vf]!), Q.2)
  (smt3Pt P[I.nA]! P[I.nB]! P[I.nD]! p.A p.B p.D, smt3Pt P[I.nD]! Q Qs p.D p.Q (p.Q + (2 * w.d + w.c - w.f)))

theorem psiY2PosN_sound {V : Array DI} {P : Array Pt} {w : Stmt.Vars} (hV : VEnc .reg V w) (hP : PEnc .reg P w)
    (h : psiY2PosN idsReg V P = true) {ω : Stmt.Wit} (h1 : ω.p1 = (psiWit V P w).1) (h2 : ω.p2 = (psiWit V P w).2) :
    0 < Stmt.psiNet w ω := by
  obtain ⟨hb, hc, hd, hs, he, hf, -⟩ := hV.get
  obtain ⟨nA, nB, nD, nP, nQ, nR, -, -, -⟩ := hP.nodes
  simp only [Stmt.ids] at hb hc hd hs he hf nA nB nD nP nQ nR
  have hQs : PtEnc (P[idsReg.nQ]!.1 + ((V[idsReg.vd]!).nmul 2 + V[idsReg.vc]! - V[idsReg.vf]!), P[idsReg.nQ]!.2)
      ((Stmt.pts w).Q + (2 * w.d + w.c - w.f)) := by
    refine ⟨Enc.congr (enc_add nQ.1 (enc_sub (enc_add (enc_nmul 2 hd) hc) hf)) ?_, Enc.congr nQ.2 ?_⟩ <;> simp
  have e1 := enc_smt3n nA nB nD
  have e2 := enc_smt3n nD nQ hQs
  have e3 := enc_dist nQ nR
  have e0 := enc_add (enc_add (enc_add (enc_add (enc_add enc_one hb) hs) (enc_nmul 3 hd)) (enc_nmul 2 hc)) he
  unfold psiY2PosN at h
  have := pos_sound (enc_sub (enc_sub (enc_sub e0 e1) e2) e3) h
  unfold Stmt.psiNet
  rw [h1, h2]
  simp only [psiWit]
  push_cast at this
  exact this

/-! ## One T* edge -/

theorem edgeKey_keyMap {I : Ids} {a b : ℕ} {K : Key} (h : S43.edgeKey I a b = some K) : (keyMap K).isSome := by
  unfold S43.edgeKey at h
  simp only at h
  repeat' (split at h)
  all_goals first | (cases h; done) | (simp only [Option.some.injEq] at h; subst h; rfl)

theorem nX_eq_nn (F : Stmt.Fam) : (Stmt.ids F).nX = Stmt.nn F := by cases F <;> rfl

theorem edgeValN_sound {F : Stmt.Fam} {fval L : ℕ} {V : Array DI} {w : Stmt.Vars} (hV : VEnc F V w)
    {ω : Stmt.Wit}
    (hω : F = .reg → fval = 3 → ω.p1 = (psiWit V (coordsN (Stmt.ids F) V) w).1 ∧
      ω.p2 = (psiWit V (coordsN (Stmt.ids F) V) w).2)
    {a b : ℕ} {z : DI} (h : edgeValN (Stmt.ids F) fval V (coordsN (Stmt.ids F) V) L a b = some z) :
    ∃ k, Stmt.tKind F L a b = some k ∧ z.Enc (Stmt.kVal F L w k) ∧ Stmt.kVcond F fval L w ω k ∧
      (k = .bnd .Y → fval = 1 ∨ (F = .reg ∧ fval = 3)) := by
  have hP := coords_enc hV
  generalize hPdef : coordsN (Stmt.ids F) V = P at hP h hω
  unfold edgeValN at h
  unfold Stmt.tKind
  by_cases hxy : a = (Stmt.ids F).nX ∨ b = (Stmt.ids F).nX ∨ a = (Stmt.ids F).nY ∨ b = (Stmt.ids F).nY
  · have hxyB : (a == (Stmt.ids F).nX || b == (Stmt.ids F).nX || a == (Stmt.ids F).nY || b == (Stmt.ids F).nY) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq]; tauto
    rw [if_pos hxyB] at h
    simp only [if_pos hxy]
    cases hk : S43.edgeKey (Stmt.ids F) a b with
    | none => rw [hk] at h; simp at h
    | some K =>
      rw [hk] at h
      simp only at h
      cases hl : lemmaEntryN (Stmt.ids F) fval V P L K with
      | none => rw [hl] at h; simp at h
      | some o =>
        cases o with
        | none => rw [hl] at h; simp at h
        | some z' =>
          rw [hl] at h; simp only [Option.some.injEq] at h; subst h
          obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp (edgeKey_keyMap hk)
          rw [stmt_edgeKey, hk]
          simp only [Option.bind_some, hK']
          by_cases hYK : K = .Y
          · -- the Y bounds (and Lemma Y2)
            subst hYK
            simp only [keyMap, Option.some.injEq] at hK'; subst hK'
            simp only [Stmt.avail, if_true]
            refine ⟨_, rfl, ?_⟩
            obtain ⟨nA, nB, nD, nP, nQ, nR, nS, nr, nUV⟩ := hP.nodes
            simp only [lemmaEntryN] at hl
            cases F
            · -- d_regular: maxdist D [P, Q]
              have hbound : z'.Enc (Stmt.maxdist (Stmt.pts w).D [(Stmt.pts w).P, (Stmt.pts w).Q]) ∧
                  (fval = 3 → psiY2PosN idsReg V P = true) ∧ (fval = 1 ∨ fval = 3) := by
                by_cases h3 : fval = 3
                · subst h3
                  simp +decide only [Stmt.ids, ↓reduceIte] at hl
                  cases hpsi : psiY2PosN idsReg V P
                  · simp [hpsi] at hl
                  · simp only [hpsi, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hl
                    subst hl
                    exact ⟨enc_maxdist P _ _ nD _ _ (by simp) (.cons nP (.cons nQ .nil)), fun _ => rfl, Or.inr rfl⟩
                · have h3' : (fval == 3) = false := by simpa using h3
                  by_cases h1 : fval = 1
                  · subst h1
                    simp +decide only [Stmt.ids, ↓reduceIte] at hl
                    simp only [Option.some.injEq] at hl; subst hl
                    exact ⟨enc_maxdist P _ _ nD _ _ (by simp) (.cons nP (.cons nQ .nil)), fun h => absurd h (by decide), Or.inl rfl⟩
                  · have h1' : (fval != 1) = true := by simpa using h1
                    simp +decide only [Stmt.ids, h3', h1', Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hl
                    simp at hl
              refine ⟨hbound.1, ?_, fun _ => hbound.2.2.elim Or.inl (fun h => Or.inr ⟨rfl, h⟩)⟩
              simp only [Stmt.kVcond]
              rintro ⟨-, h3⟩
              obtain ⟨e1, e2⟩ := hω rfl h3
              exact psiY2PosN_sound hV hP (hbound.2.1 h3) e1 e2
            · -- d_steiner: maxdist V [r, P, Q], only for f <= d
              obtain ⟨_, nV⟩ := nUV rfl
              by_cases h1 : fval = 1
              · subst h1
                simp +decide only [Stmt.ids, ↓reduceIte] at hl
                simp only [Option.some.injEq] at hl; subst hl
                refine ⟨enc_maxdist P _ _ nV _ _ (by simp) (.cons nr (.cons nP (.cons nQ .nil))), ?_, fun _ => Or.inl rfl⟩
                simp only [Stmt.kVcond]; rintro ⟨h, -⟩; cases h
              · have h1' : (fval != 1) = true := by simpa using h1
                simp +decide only [Stmt.ids, h1', ↓reduceIte, Bool.and_false, Bool.false_eq_true] at hl
                simp [idsSt] at hl
          · -- A-X, U-X, V-X, D-X
            have hl' : lemmaEntry (Stmt.ids F) fval V P L K = some (some z') := by
              cases K <;> first | exact absurd rfl hYK | exact hl
            have hKY : K' ≠ .Y := by
              intro e; subst e; cases K <;> simp [keyMap] at hK'; exact hYK rfl
            obtain ⟨hav, cb, hcb, hc1, hc2⟩ := lemmaEntry_sound hV hP hK' hKY hl'
            rw [if_pos hav]
            refine ⟨_, rfl, by simpa [Stmt.kVal, hcb] using hc2, ?_, fun e => absurd (Stmt.TermK.bnd.inj e) hKY⟩
            cases K' <;> first | exact absurd rfl hKY | simpa [Stmt.kVcond, hcb] using hc1
  · have hxyB : (a == (Stmt.ids F).nX || b == (Stmt.ids F).nX || a == (Stmt.ids F).nY || b == (Stmt.ids F).nY) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; tauto
    rw [if_neg (by simp [hxyB])] at h
    simp only [if_neg hxy]
    by_cases hr : a < (Stmt.ids F).nX ∧ b < (Stmt.ids F).nX
    · rw [if_pos (by simpa using hr)] at h
      simp only [Option.some.injEq] at h; subst h
      rw [nX_eq_nn] at hr
      rw [if_pos hr]
      exact ⟨_, rfl, enc_dist (hP a hr.1) (hP b hr.2), trivial, fun e => by cases e⟩
    · rw [if_neg (by simpa using hr)] at h; simp at h

/-! ## The S+ network -/

/-- the Steiner points of the S+ network -/
noncomputable def spWit (F : Stmt.Fam) (P : Array Pt) (sp : Split) (L : ℕ) (w : Stmt.Vars) : ℂ × ℂ :=
  let I := Stmt.ids F; let f := Stmt.pt F w
  match sp.sp.toList with
  | [a, b, c] => (smt3Pt P[a]! P[b]! P[c]! (f a) (f b) (f c), 0)
  | [_, _, _, _] =>
    let XY := if L = 3 then net4W P[I.nA]! P[I.nR]! P[I.nD]! P[I.nQ]!
      else if L = 6 then net4W P[I.nB]! P[I.nD]! P[I.nQ]! P[I.nR]!
      else net4W P[I.nA]! P[I.nD]! P[I.nQ]! P[I.nR]!
    (realPt XY.1, realPt XY.2)
  | _ => (0, 0)

theorem node_lt (F : Stmt.Fam) :
    let I := Stmt.ids F
    I.nA < Stmt.nn F ∧ I.nB < Stmt.nn F ∧ I.nD < Stmt.nn F ∧ I.nQ < Stmt.nn F ∧ I.nR < Stmt.nn F := by
  cases F <;> decide

theorem spDIN_sound {F : Stmt.Fam} {P : Array Pt} {w : Stmt.Vars} (hP : PEnc F P w) {sp : Split} {L : ℕ} {s : DI}
    (h : spDIN (Stmt.ids F) P sp L = some s) {ω : Stmt.Wit} (hx : ω.x = (spWit F P sp L w).1)
    (hy : ω.y = (spWit F P sp L w).2) :
    ∃ sk, Stmt.spKind F L sp = some sk ∧ s.Enc (Stmt.spVal F w ω sk) := by
  obtain ⟨lA, lB, lD, lQ, lR⟩ := node_lt F
  unfold spDIN at h
  unfold Stmt.spKind
  rw [nX_eq_nn] at h
  by_cases hall : (sp.sp.toList.all (· < Stmt.nn F)) = true
  swap
  · rw [if_pos (by simp [hall])] at h; cases h
  rw [if_neg (by simp [hall])] at h
  rw [if_neg (by simp [hall])]
  have hall' : ∀ i ∈ sp.sp.toList, i < Stmt.nn F := fun i hi => by simpa using List.all_eq_true.mp hall i hi
  unfold spWit at hx hy
  generalize hl : sp.sp.toList = l at h hall' hx hy
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, enc_zero⟩
  · simp only [Option.some.injEq] at h; subst h; exact ⟨_, rfl, enc_zero⟩
  · simp only [Option.some.injEq] at h; subst h
    exact ⟨_, rfl, enc_dist (hP a (hall' a (by simp))) (hP b (hall' b (by simp)))⟩
  · simp only [Option.some.injEq] at h; subst h
    refine ⟨_, rfl, ?_⟩
    simp only [Stmt.spVal, hx]
    exact enc_smt3n (hP a (hall' a (by simp))) (hP b (hall' b (by simp))) (hP c (hall' c (by simp)))
  · simp only at h hx hy ⊢
    by_cases h1 : [a, b, c, d] = sorted4 [(Stmt.ids F).nA, (Stmt.ids F).nD, (Stmt.ids F).nQ, (Stmt.ids F).nR]
    · rw [if_pos (by simpa using h1)] at h
      rw [if_pos h1]
      by_cases h3 : L = 3
      · subst h3
        simp +decide only [↓reduceIte, Option.some.injEq] at h hx hy ⊢; subst h
        refine ⟨_, rfl, ?_⟩
        simp only [Stmt.spVal, hx, hy]
        exact enc_net4n (hP _ lA) (hP _ lR) (hP _ lD) (hP _ lQ)
      · have h3' : (L == 3) = false := by simpa using h3
        rw [if_neg (by simp [h3'])] at h
        rw [if_neg h3]
        by_cases h47 : L = 4 ∨ L = 7
        · rw [if_pos (by rcases h47 with rfl | rfl <;> rfl)] at h
          rw [if_pos h47]
          simp only [Option.some.injEq] at h; subst h
          refine ⟨_, rfl, ?_⟩
          have h6 : L ≠ 6 := by omega
          simp only [Stmt.spVal, hx, hy, if_neg h3, if_neg h6]
          exact enc_net4n (hP _ lA) (hP _ lD) (hP _ lQ) (hP _ lR)
        · rw [if_neg (by simp only [Bool.or_eq_true, beq_iff_eq]; exact h47)] at h; cases h
    · rw [if_neg (by simpa using h1)] at h
      rw [if_neg h1]
      by_cases h2 : [a, b, c, d] = sorted4 [(Stmt.ids F).nB, (Stmt.ids F).nD, (Stmt.ids F).nQ, (Stmt.ids F).nR]
      · rw [if_pos (by simpa using h2)] at h
        rw [if_pos h2]
        by_cases h6 : L = 6
        · subst h6
          simp +decide only [↓reduceIte, Option.some.injEq] at h; subst h
          refine ⟨_, rfl, ?_⟩
          simp only [Stmt.spVal, hx, hy]
          simp +decide only [↓reduceIte]
          exact enc_net4n (hP _ lB) (hP _ lD) (hP _ lQ) (hP _ lR)
        · rw [if_neg (by simpa using h6)] at h; cases h
      · rw [if_neg (by simpa using h2)] at h; cases h
  · cases h

/-! ## S- -/

theorem enc_smDIN {F : Stmt.Fam} {V : Array DI} {w : Stmt.Vars} (hV : VEnc F V w) (sp : Split) :
    (smDIN V sp).Enc (Stmt.sMinus F sp w) := by
  unfold smDIN Stmt.sMinus
  suffices H : ∀ (l : List ℕ) (acc : DI) (r : ℝ), acc.Enc r →
      (l.foldl (fun acc e => acc + (if e == 0 then DI.one else V[e - 1]!)) acc).Enc
        (r + (l.map fun i => if i = 0 then 1 else Stmt.varOf F w (i - 1)).sum) by
    simpa using H sp.sm.toList DI.zero 0 enc_zero
  intro l
  induction l with
  | nil => intro acc r h; simpa using h
  | cons e l ih =>
    intro acc r h
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have he : (if e == 0 then DI.one else V[e - 1]!).Enc (if e = 0 then 1 else Stmt.varOf F w (e - 1)) := by
      by_cases h0 : e = 0
      · subst h0; simpa using enc_one
      · have : (e == 0) = false := by simpa using h0
        rw [this, if_neg h0]; exact hV (e - 1)
    exact Enc.congr (ih _ _ (enc_add h he)) (by ring)

/-! ## The vertex -/

theorem mapM_zipWith_rel {α β γ δ : Type} (f : α → β → Option γ) (g : α → β → Option δ) (R : γ → δ → Prop)
    (hfg : ∀ a b z, f a b = some z → ∃ k, g a b = some k ∧ R z k) :
    ∀ (xs : List α) (ys : List β) (zs : List γ), (List.zipWith f xs ys).mapM id = some zs →
      ∃ ks, (List.zipWith g xs ys).mapM id = some ks ∧ List.Forall₂ R zs ks := by
  intro xs
  induction xs with
  | nil => intro ys zs h; simp at h; subst h; exact ⟨[], by simp, .nil⟩
  | cons x xs ih =>
    intro ys zs h
    cases ys with
    | nil => simp at h; subst h; exact ⟨[], by simp, .nil⟩
    | cons y ys =>
      simp only [List.zipWith_cons_cons, List.mapM_cons, id] at h ⊢
      cases hf : f x y with
      | none => simp [hf] at h
      | some z =>
        cases hr : (List.zipWith f xs ys).mapM id with
        | none => simp [hf, hr] at h
        | some zs' =>
          simp [hf, hr] at h
          subst h
          obtain ⟨k, hk, hR⟩ := hfg x y z hf
          obtain ⟨ks, hks, hR'⟩ := ih ys zs' hr
          exact ⟨k :: ks, by simp [hk, hks], .cons hR hR'⟩

theorem enc_foldl_sum {f : Stmt.TermK → ℝ} : ∀ {ts : List DI} {ks : List Stmt.TermK},
    List.Forall₂ (fun z k => z.Enc (f k)) ts ks → ∀ (acc : DI) (r : ℝ), acc.Enc r →
      (ts.foldl (· + ·) acc).Enc (r + (ks.map f).sum) := by
  intro ts ks h
  induction h with
  | nil => intro acc r ha; simpa using ha
  | cons hz _ ih =>
    intro acc r ha
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    exact Enc.congr (ih _ _ (enc_add ha hz)) (by ring)

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
    ∀ b ∈ l₂, ∃ a ∈ l₁, R a b := by
  intro l₁ l₂ h
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, hR⟩ := ih b hb; exact ⟨a, List.mem_cons_of_mem _ ha, hR⟩

/-- **vertex soundness**: an accepted vertex has the network property for the checker's explicit witness -/
theorem evalVertexN_sound {F : Stmt.Fam} {fval L : ℕ} {rho : DI} {ρ : ℝ} (hrho : rho.Enc ρ) {V : Array DI}
    {w : Stmt.Vars} (hV : VEnc F V w)
    (hn : 0 ≤ w.b ∧ 0 ≤ w.c ∧ 0 ≤ w.d ∧ 0 ≤ w.s ∧ 0 ≤ w.u ∧ 0 ≤ w.v ∧ 0 ≤ w.e ∧ 0 ≤ w.f) {sp : Split}
    (h : evalVertexN (Stmt.ids F) fval rho V sp L = true) :
    ∃ ks sk, Stmt.tKinds F L sp = some ks ∧ Stmt.spKind F L sp = some sk ∧
      (∀ k ∈ ks, k = .bnd .Y → fval = 1 ∨ (F = .reg ∧ fval = 3)) ∧ ∃ ω, Stmt.vset F fval L sp ρ ks sk w ω := by
  have hP := coords_enc hV
  let ω : Stmt.Wit := ⟨(spWit F (coordsN (Stmt.ids F) V) sp L w).1, (spWit F (coordsN (Stmt.ids F) V) sp L w).2,
    (psiWit V (coordsN (Stmt.ids F) V) w).1, (psiWit V (coordsN (Stmt.ids F) V) w).2⟩
  unfold evalVertexN at h
  simp only at h
  cases hts : (List.zipWith (edgeValN (Stmt.ids F) fval V (coordsN (Stmt.ids F) V) L) sp.ta.toList sp.tb.toList).mapM id with
  | none => rw [hts] at h; simp at h
  | some ts =>
    cases hsp : spDIN (Stmt.ids F) (coordsN (Stmt.ids F) V) sp L with
    | none => rw [hts, hsp] at h; simp at h
    | some spl =>
      rw [hts, hsp] at h
      simp only at h
      obtain ⟨ks, hks, hR⟩ := mapM_zipWith_rel _ (Stmt.tKind F L)
        (fun z k => z.Enc (Stmt.kVal F L w k) ∧ Stmt.kVcond F fval L w ω k ∧
          (k = .bnd .Y → fval = 1 ∨ (F = .reg ∧ fval = 3)))
        (fun a b z hz => edgeValN_sound hV (ω := ω) (fun _ _ => ⟨rfl, rfl⟩) hz) _ _ _ hts
      obtain ⟨sk, hsk, hspe⟩ := spDIN_sound hP hsp (ω := ω) rfl rfl
      refine ⟨ks, sk, hks, hsk, fun k hk => (forall₂_mem_right hR k hk).choose_spec.2.2.2, ω, hn, ?_, ?_⟩
      · intro k hk
        obtain ⟨z, -, hzk⟩ := forall₂_mem_right hR k hk
        exact hzk.2.1
      · have hsum := enc_foldl_sum (hR.imp (fun _ _ h => h.1)) DI.zero 0 enc_zero
        have := nonpos_sound (enc_sub (enc_add (enc_mul hrho hsum) hspe) (enc_smDIN hV sp)) h
        unfold Stmt.gNet
        simpa using this

end S43
