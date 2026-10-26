module

public import VertexSoundK
public import S43CoreK.CheckK
public import S43.Sound.Target

@[expose] public section

/-! # K2: soundness of `checkRecordK` (mirror of lean/'s `checkRecord_ok` / `checkRecord_good`,
S43/Sound/Record.lean and Target.lean)

Uses K1 (`evalVertexK_sound`, VertexSoundK.lean) at every vertex of the finite face, then lean/'s semantic
lemmas unchanged:
`S43.Stmt.vset_box` (convexity), `S43.Stmt.vset_unbounded` (infinite sides), `S43.Stmt.vset_bump` (f := d), `MonoData`.
Facts about the split table enter as hypotheses (`hglue`, `hlen`); they are kernel-decided separately (K0 + SplitsK).
Box values enter the vertex values as `ofMantS m s = ofMant m` (salted, exact; within 2^126 by `allBelow`). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- lean/'s `InBox` for the kernel box (lower ends `lo/2^P`, upper ends `hi/2^P` or none = +infinity) -/
def InBoxK (bx : BoxK) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, ((lget bx.lo j : ℕ) : ℝ) / 2 ^ S43.P ≤ x j ∧
    ∀ h : ℕ, hget bx.hi j = some h → x j ≤ (h : ℝ) / 2 ^ S43.P

/-! ## Helpers: salted box ends, the vertex loop, the vertex values -/

theorem ofMantS_eq (m s : ℕ) : ofMantS m s = DN.ofMant m := by
  unfold ofMantS DN.ofMant
  simp only [Nat.add_eq, Nat.sub_eq, Nat.add_sub_cancel]

/-- `vs` is a vertex of the finite face: each coordinate at its lower end, or at its finite upper end -/
def VertexOf : List ℕ → List (Option ℕ) → List ℕ → Prop
  | [], [], [] => True
  | l :: ls, h :: hs, v :: vs => (v = l ∨ h = some v) ∧ VertexOf ls hs vs
  | _, _, _ => False

theorem VertexOf.length : ∀ {lo : List ℕ} {hi : List (Option ℕ)} {vs : List ℕ}, VertexOf lo hi vs →
    vs.length = lo.length
  | [], [], [], _ => rfl
  | _ :: _, _ :: _, _ :: _, h => by simp only [List.length_cons]; rw [VertexOf.length h.2]
  | [], _ :: _, _, h => by simp [VertexOf] at h
  | [], [], _ :: _, h => by simp [VertexOf] at h
  | _ :: _, [], _, h => by simp [VertexOf] at h
  | _ :: _, _ :: _, [], h => by simp [VertexOf] at h

/-- the vertex loop visits every vertex (mirror of lean/'s `allVerts_sound`; salts are value-neutral) -/
theorem allVK_sound (ev : List DN → Bool) : ∀ (lo : List ℕ) (hi : List (Option ℕ)) (j : ℕ) (acc : List DN),
    allVK ev j lo hi acc = true → ∀ vs, VertexOf lo hi vs → ev ((vs.map DN.ofMant).reverse ++ acc) = true
  | [], [], j, acc, h, vs, hv => by
    cases vs with
    | nil => simpa [allVK] using h
    | cons _ _ => simp [VertexOf] at hv
  | l :: ls, hh :: hs, j, acc, h, vs, hv => by
    cases vs with
    | nil => simp [VertexOf] at hv
    | cons v vs =>
      obtain ⟨hvc, hvs⟩ := hv
      simp only [allVK, Bool.and_eq_true] at h
      obtain ⟨hlo, hhi⟩ := h
      rcases hvc with rfl | rfl
      · have := allVK_sound ev ls hs _ _ hlo vs hvs
        rw [ofMantS_eq] at this
        simpa [List.map_cons, List.reverse_cons, List.append_assoc] using this
      · have := allVK_sound ev ls hs _ _ hhi vs hvs
        rw [ofMantS_eq] at this
        simpa [List.map_cons, List.reverse_cons, List.append_assoc] using this
  | [], _ :: _, j, acc, h, vs, hv => by cases vs <;> simp [VertexOf] at hv
  | _ :: _, [], j, acc, h, vs, hv => by cases vs <;> simp [VertexOf] at hv

/-- box ends below 2^126 -/
theorem allBelow_mem : ∀ {l : List ℕ}, allBelow l = true → ∀ x ∈ l, x < 2 ^ 126
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    simp only [allBelow, Bool.and_eq_true, Nat.blt_eq] at h
    have hMB : MB = 2 ^ 126 := by decide
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [← hMB]; exact h.1
    · exact allBelow_mem h.2 x hx

theorem allBelowO_mem : ∀ {l : List (Option ℕ)}, allBelowO l = true → ∀ x, some x ∈ l → x < 2 ^ 126
  | [], _, x, hx => by simp at hx
  | none :: l, h, x, hx => by
    simp only [allBelowO] at h
    rcases List.mem_cons.1 hx with e | hx
    · exact absurd e (by simp)
    · exact allBelowO_mem h x hx
  | some a :: l, h, x, hx => by
    simp only [allBelowO, Bool.and_eq_true, Nat.blt_eq] at h
    have hMB : MB = 2 ^ 126 := by decide
    rcases List.mem_cons.1 hx with e | hx
    · simp only [Option.some.injEq] at e; subst e; rw [← hMB]; exact h.1
    · exact allBelowO_mem h.2 x hx

/-- a vertex's values are box ends, hence below 2^126 -/
theorem VertexOf.bound : ∀ {lo : List ℕ} {hi : List (Option ℕ)} {vs : List ℕ}, VertexOf lo hi vs →
    allBelow lo = true → allBelowO hi = true → ∀ v ∈ vs, v < 2 ^ 126
  | [], [], [], _, _, _, v, hv => by simp at hv
  | l :: ls, h :: hs, x :: vs, hvx, hl, hh, v, hv => by
    have hl' := allBelow_mem hl
    have hh' := allBelowO_mem hh
    rcases List.mem_cons.1 hv with rfl | hv
    · rcases hvx.1 with rfl | e
      · exact hl' _ List.mem_cons_self
      · exact hh' _ (by rw [← e]; exact List.mem_cons_self)
    · simp only [allBelow, Bool.and_eq_true] at hl
      cases h with
      | none => simp only [allBelowO] at hh; exact VertexOf.bound hvx.2 hl.2 hh v hv
      | some a => simp only [allBelowO, Bool.and_eq_true] at hh; exact VertexOf.bound hvx.2 hl.2 hh.2 v hv
  | [], _ :: _, _, hv, _, _, _, _ => by simp [VertexOf] at hv
  | [], [], _ :: _, hv, _, _, _, _ => by simp [VertexOf] at hv
  | _ :: _, [], _, hv, _, _, _, _ => by simp [VertexOf] at hv
  | _ :: _, _ :: _, [], hv, _, _, _, _ => by simp [VertexOf] at hv

/-- the real value of a box end -/
theorem eb_end {m : ℕ} (hm : m < 2 ^ 126) : EB 126 (DN.ofMant m) ((m : ℝ) / 2 ^ S43.P) := by
  have h := eb_ofMant hm
  exact h.congr (by push_cast; rfl)

/-- the vertex values of a vertex `vs` enclose the case variables of its real point (mirror of lean/'s
`vertexV_enc`) -/
theorem vEncK_vertex {st : Bool} {fval : ℕ} (hf2 : fval = 2 → st = true) {vs : List ℕ}
    (hlen : vs.length = S43.Stmt.nbOf (famOf st) fval) (hb : ∀ v ∈ vs, v < 2 ^ 126) :
    VEncK st (mkVars st ((vs.map DN.ofMant).reverse))
      (S43.Stmt.embed (famOf st) fval (fun i => ((vs.getD i 0 : ℕ) : ℝ) / 2 ^ S43.P)) := by
  by_cases h2 : fval = 2
  · obtain rfl := hf2 h2
    subst h2
    have hl7 : vs.length = 7 := by simpa [famOf, S43.Stmt.nbOf] using hlen
    rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨s, _ | ⟨u, _ | ⟨v, _ | ⟨e, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at hl7 <;> try omega
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, mkVars]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
      simp only [S43.Stmt.embed, famOf, S43.Stmt.nbOf] <;>
      first
      | exact (eb_end (hb _ (by simp))).congr (by simp)
      | skip
  · cases st
    · have hl6 : vs.length = 6 := by simpa [famOf, S43.Stmt.nbOf, h2] using hlen
      rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨s, _ | ⟨e, _ | ⟨f, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;>
        simp only [List.length_cons, List.length_nil] at hl6 <;> try omega
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, mkVars, Bool.cond_false]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h (by simp)⟩ <;>
        simp only [S43.Stmt.embed, famOf, S43.Stmt.nbOf, h2, ↓reduceIte] <;>
        first
        | exact (eb_end (hb _ (by simp))).congr (by simp [h2])
        | skip
    · have hl8 : vs.length = 8 := by simpa [famOf, S43.Stmt.nbOf, h2] using hlen
      rcases vs with _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨s, _ | ⟨u, _ | ⟨v, _ | ⟨e, _ | ⟨f, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp only [List.length_cons, List.length_nil] at hl8 <;> try omega
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, mkVars]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, ?_⟩⟩ <;>
        simp only [S43.Stmt.embed, famOf, S43.Stmt.nbOf, h2, ↓reduceIte] <;>
        first
        | exact (eb_end (hb _ (by simp))).congr (by simp [h2])
        | skip

/-- a vertex from coordinatewise choices -/
theorem vertexOf_of_getD : ∀ (lo : List ℕ) (hi : List (Option ℕ)) (vs : List ℕ),
    hi.length = lo.length → vs.length = lo.length →
    (∀ i < lo.length, vs.getD i 0 = lget lo i ∨ hget hi i = some (vs.getD i 0)) → VertexOf lo hi vs
  | [], [], [], _, _, _ => trivial
  | l :: ls, h :: hs, v :: vs, e1, e2, hv => by
    refine ⟨?_, vertexOf_of_getD ls hs vs (by simpa using e1) (by simpa using e2) (fun i hi => ?_)⟩
    · simpa [lget, hget] using hv 0 (by simp)
    · simpa [lget, hget] using hv (i + 1) (by simp; omega)
  | [], _ :: _, _, e1, _, _ => by simp at e1
  | _ :: _, [], _, e1, _, _ => by simp at e1
  | [], [], _ :: _, _, e2, _ => by simp at e2
  | _ :: _, _ :: _, [], _, e2, _ => by simp at e2

/-! ## The kernel split predicates are those of lean/ -/

theorem nYK_eq (st : Bool) : nYK st = (S43.Stmt.ids (famOf st)).nY := by cases st <;> rfl
theorem nXK_eq' (st : Bool) : nXK st = (S43.Stmt.ids (famOf st)).nX := by cases st <;> rfl
theorem vfK_eq (st : Bool) : vfK st = (S43.Stmt.ids (famOf st)).vf := by cases st <;> rfl
theorem nQK_eq (st : Bool) : nQK st = (S43.Stmt.ids (famOf st)).nQ := by cases st <;> rfl
theorem nA_eq (st : Bool) : (S43.Stmt.ids (famOf st)).nA = 0 := by cases st <;> rfl

theorem bitK_eq (m i : ℕ) : bitK m i = S43.bit m i := by
  unfold bitK S43.bit
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
  exact Iff.rfl

theorem hasYK_eq (st : Bool) : ∀ ta tb : List ℕ,
    hasYK st ta tb = (List.zip ta tb).any (fun e => e.1 == (S43.Stmt.ids (famOf st)).nY || e.2 == (S43.Stmt.ids (famOf st)).nY)
  | [], _ => by simp [hasYK]
  | _ :: _, [] => by simp [hasYK]
  | a :: as, b :: bs => by
    simp only [hasYK, List.zip_cons_cons, List.any_cons, hasYK_eq st as bs, nYK_eq, Bool.or_assoc]
    rfl

theorem hasAXK_eq (st : Bool) : ∀ ta tb : List ℕ,
    hasAXK st ta tb = (List.zip ta tb).any (fun e =>
      (e.1 == (S43.Stmt.ids (famOf st)).nX && e.2 == (S43.Stmt.ids (famOf st)).nA) ||
      (e.1 == (S43.Stmt.ids (famOf st)).nA && e.2 == (S43.Stmt.ids (famOf st)).nX))
  | [], _ => by simp [hasAXK]
  | _ :: _, [] => by simp [hasAXK]
  | a :: as, b :: bs => by
    simp only [hasAXK, List.zip_cons_cons, List.any_cons, hasAXK_eq st as bs, nXK_eq', nA_eq, Bool.or_assoc]
    rfl

theorem hasYK_toSplit (st : Bool) (sp : SplitK) :
    hasYK st sp.ta sp.tb = S43.hasY (S43.Stmt.ids (famOf st)) (toSplit sp) := by
  rw [hasYK_eq]; unfold S43.hasY toSplit; simp only [List.toList_toArray]

theorem hasAXK_toSplit (st : Bool) (sp : SplitK) :
    hasAXK st sp.ta sp.tb = S43.hasAX (S43.Stmt.ids (famOf st)) (toSplit sp) := by
  rw [hasAXK_eq]; unfold S43.hasAX toSplit; simp only [List.toList_toArray]

theorem memK_eq (x : ℕ) : ∀ l : List ℕ, memK x l = l.contains x
  | [] => rfl
  | a :: l => by
    simp only [memK, List.contains_cons, memK_eq x l]
    congr 1
    rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]
    exact eq_comm

theorem extOKK_toSplit (st : Bool) (sp : SplitK) :
    extOKK st sp = S43.extOK (S43.Stmt.ids (famOf st)) (toSplit sp) := by
  unfold extOKK S43.extOK toSplit
  simp only [memK_eq, ← Array.contains_toList, List.toList_toArray, nQK_eq, vfK_eq, Nat.add_eq]

/-! ## The verdicts -/

theorem checkSp_cases (st : Bool) (fval nb L : ℕ) (sp : SplitK) (bx : BoxK) :
    checkSp st fval nb L sp bx = .ok ∨ checkSp st fval nb L sp bx = .fail := by
  unfold checkSp
  cases (allBelow bx.lo && allBelowO bx.hi && staticOKK st fval nb sp L bx && checkVerts st fval L sp bx)
  · right; rfl
  · left; rfl

theorem cond_ok {c : Bool} {v : VerdictK} (hv : v ≠ .ok) (h : (bif c then VerdictK.ok else v) = .ok) : c = true := by
  cases c
  · exact absurd h hv
  · rfl

/-- what a non-fail verdict gives -/
theorem checkRecordK_spec {st : Bool} {fval nb : ℕ} {bx : BoxK} {sid lid : ℕ}
    (h : checkRecordK st fval nb bx sid lid ≠ .fail) :
    (checkRecordK st fval nb bx sid lid = .skipSym ∧ skipSymK st bx = true) ∨
    (checkRecordK st fval nb bx sid lid = .skipSub ∧ skipSubK st fval bx = true) ∨
    (checkRecordK st fval nb bx sid lid = .ok ∧ bx.lo.length = nb ∧ bx.hi.length = nb ∧ 1 ≤ sid ∧
      sid ≤ nSplits st ∧ lid ≤ 8 ∧ checkSp st fval nb lid (splitK st sid) bx = .ok) := by
  revert h
  unfold checkRecordK
  cases e : (!(Nat.beq bx.lo.length nb) || !(Nat.beq bx.hi.length nb)) with
  | true => intro h; exact absurd rfl h
  | false =>
    have e' : Nat.beq bx.lo.length nb = true ∧ Nat.beq bx.hi.length nb = true := by
      cases a1 : Nat.beq bx.lo.length nb <;> cases a2 : Nat.beq bx.hi.length nb <;> rw [a1, a2] at e <;>
        first | exact ⟨rfl, rfl⟩ | exact absurd e (by decide)
    cases e3 : skipSymK st bx with
    | true => intro _; exact Or.inl ⟨rfl, rfl⟩
    | false =>
      cases e4 : skipSubK st fval bx with
      | true => intro _; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | false =>
        cases e5 : (Nat.beq sid 0 || Nat.blt (nSplits st) sid || Nat.blt 8 lid) with
        | true => intro h; exact absurd rfl h
        | false =>
          intro h
          have e5' : Nat.beq sid 0 = false ∧ Nat.blt (nSplits st) sid = false ∧ Nat.blt 8 lid = false := by
            cases a1 : Nat.beq sid 0 <;> cases a2 : Nat.blt (nSplits st) sid <;> cases a3 : Nat.blt 8 lid <;>
              rw [a1, a2, a3] at e5 <;> first | exact ⟨rfl, rfl, rfl⟩ | exact absurd e5 (by decide)
          have hs1 : 1 ≤ sid := Nat.pos_of_ne_zero (Nat.ne_of_beq_eq_false e5'.1)
          have hs2 : sid ≤ nSplits st := Nat.not_lt.1 fun hc => by
            have := e5'.2.1; rw [Nat.blt_eq.mpr hc] at this; exact absurd this (by decide)
          have hl8 : lid ≤ 8 := Nat.not_lt.1 fun hc => by
            have := e5'.2.2; rw [Nat.blt_eq.mpr hc] at this; exact absurd this (by decide)
          rcases checkSp_cases st fval nb lid (splitK st sid) bx with e6 | e6
          · exact Or.inr (Or.inr ⟨e6, Nat.eq_of_beq_eq_true e'.1, Nat.eq_of_beq_eq_true e'.2, hs1, hs2, hl8, e6⟩)
          · exact absurd e6 h

/-! ## The static checks -/

/-- the box ends as reals (lean/'s `loR` / `hiR`) -/
noncomputable def loK (bx : BoxK) (j : ℕ) : ℝ := ((lget bx.lo j : ℕ) : ℝ) / 2 ^ S43.P
noncomputable def hiK (bx : BoxK) (j : ℕ) : Option ℝ := (hget bx.hi j).map fun h : ℕ => (h : ℝ) / 2 ^ S43.P

theorem allSides_spec {st : Bool} {fval : ℕ} {sp : SplitK} {L : ℕ} {bx : BoxK} :
    ∀ n, allSides st fval sp L bx n = true → ∀ k < n, sideOKK st fval sp L bx k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    simp only [allSides, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allSides_spec n h.2 k hk
    · exact h.1

theorem anyInf_false : ∀ {hs : List (Option ℕ)}, anyInf hs = false → ∀ i < hs.length, hget hs i ≠ none
  | [], _, i, hi => absurd hi (by simp)
  | none :: _, h, _, _ => by simp [anyInf] at h
  | some _ :: _, _, 0, _ => by simp [hget]
  | some _ :: hs, h, i + 1, hi => by
    simp only [anyInf] at h
    have := anyInf_false h i (by simpa using hi)
    simpa [hget] using this

/-- an infinite side: what `sideOKK` requires (mirror of lean/'s `sideOK_spec`) -/
theorem sideOKK_spec {st : Bool} {fval : ℕ} {sp : SplitK} {L : ℕ} {bx : BoxK} {j : ℕ}
    (h : sideOKK st fval sp L bx j = true) (hn : hget bx.hi j = none) :
    if fval = 3 ∧ j = vfK st then hasYK st sp.ta sp.tb = false ∧ extOKK st sp = true
    else bitK sp.mono j = true ∧ L = 0 := by
  unfold sideOKK at h
  rw [hn] at h
  simp only at h
  cases hc : (Nat.beq fval 3 && Nat.beq j (vfK st)) with
  | false =>
    rw [hc, Bool.cond_false] at h
    have c : ¬ (fval = 3 ∧ j = vfK st) := by
      rintro ⟨rfl, rfl⟩; simp [Nat.beq_refl] at hc
    rw [if_neg c]
    simpa using h
  | true =>
    rw [hc, Bool.cond_true] at h
    have c : fval = 3 ∧ j = vfK st := by simpa using hc
    rw [if_pos c]
    simpa using h

theorem nmax_eq (a b : ℕ) : nmax a b = max a b := by
  unfold nmax
  cases h : Nat.ble a b
  · rw [Bool.cond_false]
    have : ¬ a ≤ b := fun hab => by rw [Nat.ble_eq.mpr hab] at h; exact absurd h (by decide)
    exact (max_eq_left (by omega)).symm
  · rw [Bool.cond_true]
    exact (max_eq_right (Nat.ble_eq.mp h)).symm

/-! ## The record theorem -/

theorem checkRecordK_ok {st : Bool} {fval : ℕ} (hf2 : fval = 2 → st = true) {ρ : ℝ} (hrho : (toDI RHO).Enc ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : S43.MonoData (famOf st) fval)
    (hglue : ∀ i, 1 ≤ i → i ≤ nSplits st → toSplit (splitK st i) = (S43.Stmt.splits (famOf st))[i - 1]!)
    (hsize : (S43.Stmt.splits (famOf st)).size = nSplits st)
    (hlen : ∀ i, 1 ≤ i → i ≤ nSplits st → (splitK st i).ta.length ≤ 40 ∧ (splitK st i).sm.length ≤ 40)
    {bx : BoxK} {sid lid : ℕ}
    (h : checkRecordK st fval (S43.Stmt.nbOf (famOf st) fval) bx sid lid = .ok) :
    ∃ sp ∈ S43.Stmt.splits (famOf st), ∃ L ≤ 8, ∃ ks sk, S43.Stmt.tKinds (famOf st) L sp = some ks ∧
      S43.Stmt.spKind (famOf st) L sp = some sk ∧
      (∀ k ∈ ks, k = .bnd .Y → fval = 1 ∨ (famOf st = .reg ∧ fval = 3)) ∧
      (fval = 2 → S43.Stmt.monoRule (famOf st) L .f sp ks sk = true) ∧
      ∀ x : Fin (S43.Stmt.nbOf (famOf st) fval) → ℝ, InBoxK bx x →
        ∃ ω, S43.Stmt.vset (famOf st) fval L sp ρ ks sk (S43.Stmt.embed (famOf st) fval x) ω := by
  have hnf : checkRecordK st fval (S43.Stmt.nbOf (famOf st) fval) bx sid lid ≠ VerdictK.fail := by
    rw [h]; decide
  rcases checkRecordK_spec hnf with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, hlo2, hhi2, hs1, hs2, hl8, hsp⟩
  · rw [h] at e; exact absurd e (by decide)
  · rw [h] at e; exact absurd e (by decide)
  have hglue' := hglue sid hs1 hs2
  obtain ⟨hta, hsm⟩ := hlen sid hs1 hs2
  generalize hsK : splitK st sid = sK at hglue' hta hsm hsp
  unfold checkSp at hsp
  have hc := cond_ok (by decide) hsp
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hb1, hb2⟩, hst⟩, hcv⟩ := hc
  have hidx : sid - 1 < (S43.Stmt.splits (famOf st)).size := by rw [hsize]; omega
  have hspm : toSplit sK ∈ S43.Stmt.splits (famOf st) := by
    rw [hglue', getElem!_pos (S43.Stmt.splits (famOf st)) (sid - 1) hidx]; exact Array.getElem_mem hidx
  -- the static checks
  unfold staticOKK at hst
  simp only [Bool.and_eq_true] at hst
  obtain ⟨⟨⟨hFV2, hside⟩, hY3⟩, hAX⟩ := hst
  have hFV2' : fval = 2 → S43.bit (toSplit sK).mono (S43.Stmt.ids (famOf st)).vf = true := fun e => by
    subst e
    simp only [Nat.beq_refl, Bool.not_true, Bool.false_or] at hFV2
    rw [← vfK_eq, ← bitK_eq]; exact hFV2
  have hY3' : fval = 3 → S43.hasY (S43.Stmt.ids (famOf st)) (toSplit sK) = true →
      ∀ i < S43.Stmt.nbOf (famOf st) fval, hget bx.hi i ≠ none := by
    intro e hy i hi hn
    rw [← hasYK_toSplit] at hy
    have hai : anyInf bx.hi = false := by
      subst e; simpa [Nat.beq_refl, hy] using hY3
    exact anyInf_false hai i (by rw [hhi2]; exact hi) hn
  have hAX' : S43.hasAX (S43.Stmt.ids (famOf st)) (toSplit sK) = true → hget bx.hi 1 ≠ none := by
    intro ha hn
    rw [← hasAXK_toSplit] at ha
    simp [ha, hn] at hAX
  unfold checkVerts at hcv
  -- every vertex of the finite face is accepted
  have hvx : ∀ x : Fin (S43.Stmt.nbOf (famOf st) fval) → ℝ,
      (∀ i, x i = loK bx i ∨ x i = (hiK bx i).getD (loK bx i)) →
      ∃ ks' sk', S43.Stmt.tKinds (famOf st) lid (toSplit sK) = some ks' ∧
        S43.Stmt.spKind (famOf st) lid (toSplit sK) = some sk' ∧
        (∀ k ∈ ks', k = .bnd .Y → fval = 1 ∨ (famOf st = .reg ∧ fval = 3)) ∧
        ∃ ω, S43.Stmt.vset (famOf st) fval lid (toSplit sK) ρ ks' sk' (S43.Stmt.embed (famOf st) fval x) ω := by
    intro x hx
    classical
    obtain ⟨ch, hch⟩ : ∃ ch : ℕ → ℕ, ∀ j (hj : j < S43.Stmt.nbOf (famOf st) fval),
        ch j = if x ⟨j, hj⟩ = loK bx j then lget bx.lo j else (hget bx.hi j).getD (lget bx.lo j) :=
      ⟨fun j => if hj : j < S43.Stmt.nbOf (famOf st) fval then
        (if x ⟨j, hj⟩ = loK bx j then lget bx.lo j else (hget bx.hi j).getD (lget bx.lo j)) else 0,
       fun j hj => by simp only [dif_pos hj]⟩
    obtain ⟨vs, hvs⟩ : ∃ vs : List ℕ, vs = (List.range (S43.Stmt.nbOf (famOf st) fval)).map ch := ⟨_, rfl⟩
    have hvsl : vs.length = S43.Stmt.nbOf (famOf st) fval := by rw [hvs]; simp
    have hvsg : ∀ i < S43.Stmt.nbOf (famOf st) fval, vs.getD i 0 = ch i := fun i hi => by
      rw [hvs]; simp [List.getD_eq_getElem?_getD, hi]
    have hV : VertexOf bx.lo bx.hi vs := by
      refine vertexOf_of_getD _ _ _ (by rw [hhi2, hlo2]) (by rw [hvsl, hlo2]) (fun i hi => ?_)
      rw [hlo2] at hi
      rw [hvsg i hi, hch i hi]
      split_ifs with e
      · left; rfl
      · right
        cases hh : hget bx.hi i with
        | none =>
          exfalso
          rcases hx ⟨i, hi⟩ with e' | e'
          · exact e e'
          · apply e; rw [e']; simp [hiK, hh]
        | some h0 => rfl
    have hxe : (fun i : Fin (S43.Stmt.nbOf (famOf st) fval) => ((vs.getD i 0 : ℕ) : ℝ) / 2 ^ S43.P) = x := by
      funext ⟨i, hin⟩
      simp only []
      rw [hvsg i hin, hch i hin]
      split_ifs with e
      · rw [e]; rfl
      · rcases hx ⟨i, hin⟩ with e' | e'
        · exact absurd e' e
        · cases hh : hget bx.hi i with
          | none => exfalso; apply e; rw [e']; simp [hiK, hh]
          | some h0 => rw [e']; simp [hiK, hh]
    have hxnn : ∀ j, 0 ≤ x j := fun j => by
      have e := congrFun hxe j
      rw [← e]; positivity
    have hall := allVK_sound _ bx.lo bx.hi 0 [] hcv vs hV
    simp only [List.append_nil] at hall
    have hW := vEncK_vertex hf2 hvsl (VertexOf.bound hV hb1 hb2)
    rw [hxe] at hW
    exact evalVertexK_sound hW hrho (S43.embed_nonneg x hxnn) hta hsm hall
  -- the term kinds, from the lowest vertex
  obtain ⟨ks, sk, hks, hsk, hYk, -⟩ := hvx (fun j => loK bx j) (fun i => Or.inl rfl)
  have hvert : ∀ x : Fin (S43.Stmt.nbOf (famOf st) fval) → ℝ,
      (∀ i, x i = loK bx i ∨ x i = (hiK bx i).getD (loK bx i)) →
      ∃ ω, S43.Stmt.vset (famOf st) fval lid (toSplit sK) ρ ks sk (S43.Stmt.embed (famOf st) fval x) ω := by
    intro x hx
    obtain ⟨ks', sk', hks', hsk', -, hv⟩ := hvx x hx
    rw [hks] at hks'; rw [hsk] at hsk'
    cases hks'; cases hsk'
    exact hv
  have hface := S43.Stmt.vset_box hρ0 (fun j => loK bx j) (fun j => (hiK bx j).getD (loK bx j)) hvert
  have hmono' := hmono (toSplit sK) hspm lid hl8 ks sk hks hsk
  have hf2mono : fval = 2 → S43.Stmt.monoRule (famOf st) lid .f (toSplit sK) ks sk = true :=
    fun e => hmono'.1 e (hFV2' e)
  refine ⟨toSplit sK, hspm, lid, hl8, ks, sk, hks, hsk, hYk, hf2mono, fun x hx => ?_⟩
  refine S43.Stmt.vset_unbounded hρ0 hρ1 (fun j => loK bx j) (fun j => hiK bx j) hface (fun j hj => ?_) x
    (fun j => ⟨(hx j).1, fun hh e => ?_⟩)
  · -- an infinite side: the step conditions
    have hnone : hget bx.hi j = none := by
      simp only [hiK] at hj
      cases e : hget bx.hi j with
      | none => rfl
      | some _ => rw [e] at hj; simp at hj
    have hsj := sideOKK_spec (allSides_spec _ hside j j.isLt) hnone
    have hvf : S43.Stmt.vrOf (famOf st) (S43.Stmt.ids (famOf st)).vf = .f := by cases st <;> rfl
    refine ⟨?_, ?_, fun hc hk => ?_, fun hr hk => ?_, fun e => hf2mono e.1⟩
    · split_ifs at hsj with c
      · right; rw [c.2, vfK_eq, hvf]
      · left; exact hsj.2
    · split_ifs at hsj with c
      · rw [c.2, vfK_eq, hvf]
        exact hmono'.2.2 c.1 (by rw [← hasYK_toSplit]; exact hsj.1) (by rw [← extOKK_toSplit]; exact hsj.2)
      · rw [hsj.2]
        exact hmono'.2.1 hsj.2 j j.isLt (by rwa [vfK_eq] at c) (by rw [← bitK_eq]; exact hsj.1)
    · -- the c side: no A-X edge
      have hj1 : (j : ℕ) = 1 := S43.vrOf_c hc
      exact hAX' (S43.hasAX_of_mem hks hk) (by rw [← hj1]; exact hnone)
    · exact hY3' hr.2 (S43.hasY_of_mem hks hk) j j.isLt hnone
  · -- a finite upper end
    simp only [hiK] at e
    cases e' : hget bx.hi j with
    | none => rw [e'] at e; simp at e
    | some h0 =>
      rw [e'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [← e]; exact (hx j).2 h0 e'

theorem checkRecordK_good {st : Bool} {fval : ℕ}
    (hcase : (st = true ∧ (fval = 1 ∨ fval = 2)) ∨ (st = false ∧ (fval = 1 ∨ fval = 3))) {ρ : ℝ}
    (hrho : (toDI RHO).Enc ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : S43.MonoData (famOf st) fval)
    (hglue : ∀ i, 1 ≤ i → i ≤ nSplits st → toSplit (splitK st i) = (S43.Stmt.splits (famOf st))[i - 1]!)
    (hsize : (S43.Stmt.splits (famOf st)).size = nSplits st)
    (hlen : ∀ i, 1 ≤ i → i ≤ nSplits st → (splitK st i).ta.length ≤ 40 ∧ (splitK st i).sm.length ≤ 40)
    {bx : BoxK} {sid lid : ℕ}
    (h : checkRecordK st fval (S43.Stmt.nbOf (famOf st) fval) bx sid lid ≠ .fail) :
    ∀ w, InBoxK bx (S43.proj (famOf st) fval w) → S43.Good (famOf st) fval ρ w := by
  have hf2 : fval = 2 → st = true := fun e => by rcases hcase with ⟨h1, _⟩ | ⟨_, h3 | h3⟩ <;> simp_all
  have hP : S43.P = 100 := rfl
  intro w hx hd hs
  have hp : (0 : ℝ) < 2 ^ S43.P := by positivity
  rcases checkRecordK_spec h with ⟨-, h2⟩ | ⟨-, h3⟩ | ⟨hv, -⟩
  · -- skipSym: outside max(u, v) ≤ max(b, 1)
    exfalso
    unfold skipSymK at h2
    cases st
    · simp at h2
    · simp only [Bool.true_and] at h2
      change InBoxK bx (S43.proj .st fval w) at hx
      change S43.Stmt.domain .st w at hd
      cases e : hget bx.hi 0 with
      | none => rw [e] at h2; simp at h2
      | some hb =>
        rw [e] at h2
        simp only [Nat.blt_eq, nmax_eq] at h2
        have nb5 : 5 < S43.Stmt.nbOf .st fval := by simp only [S43.Stmt.nbOf]; split_ifs <;> decide
        have hb' := (hx ⟨0, by omega⟩).2 hb e
        have hu' := (hx ⟨4, by omega⟩).1
        have hv' := (hx ⟨5, by omega⟩).1
        simp only [S43.proj, S43.Stmt.varOf, List.getD_cons_zero, List.getD_cons_succ] at hb' hu' hv'
        have hdom := hd.2.2.2.2.2.2.2.2
        simp only at hdom
        have h2r := (Nat.cast_lt (α := ℝ)).mpr h2
        rw [Nat.cast_max, Nat.cast_max] at h2r
        have e2 : ((1267650600228229401496703205376 : ℕ) : ℝ) = 2 ^ S43.P := by rw [hP]; norm_num
        rw [e2] at h2r
        have key : Max.max ((hb : ℝ) / 2 ^ S43.P) 1 <
            Max.max ((lget bx.lo 4 : ℝ) / 2 ^ S43.P) ((lget bx.lo 5 : ℝ) / 2 ^ S43.P) := by
          have e1 : Max.max ((hb : ℝ) / 2 ^ S43.P) 1 = Max.max (hb : ℝ) (2 ^ S43.P) / 2 ^ S43.P := by
            rw [← max_div_div_right hp.le, div_self hp.ne']
          rw [e1, max_div_div_right hp.le]
          exact div_lt_div_of_pos_right h2r hp
        have : Max.max w.b 1 ≤ Max.max ((hb : ℝ) / 2 ^ S43.P) 1 := max_le_max hb' (le_refl 1)
        have : Max.max ((lget bx.lo 4 : ℝ) / 2 ^ S43.P) ((lget bx.lo 5 : ℝ) / 2 ^ S43.P) ≤
            Max.max w.u w.v :=
          max_le_max hu' hv'
        linarith
  · -- skipSub: outside the subcase
    exfalso
    unfold skipSubK at h3
    simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h3
    rcases h3 with ⟨e1, h3⟩ | ⟨e3, h3⟩
    · subst e1
      cases e : hget bx.hi 2 with
      | none => rw [e] at h3; simp at h3
      | some hd' =>
        rw [e] at h3
        simp only [Nat.blt_eq] at h3
        have hfd : w.f ≤ w.d := by simpa [S43.subcase] using hs
        have hr : ((hd' : ℕ) : ℝ) / 2 ^ S43.P < ((lget bx.lo (vfK st) : ℕ) : ℝ) / 2 ^ S43.P :=
          div_lt_div_of_pos_right (by exact_mod_cast h3) hp
        cases st
        · change InBoxK bx (S43.proj .reg 1 w) at hx
          have a1 := (hx ⟨2, by decide⟩).2 hd' e
          have a2 := (hx ⟨5, by decide⟩).1
          simp only [S43.proj, S43.Stmt.varOf, List.getD_cons_zero, List.getD_cons_succ] at a1 a2
          change _ < ((lget bx.lo 5 : ℕ) : ℝ) / 2 ^ S43.P at hr
          linarith
        · change InBoxK bx (S43.proj .st 1 w) at hx
          have a1 := (hx ⟨2, by decide⟩).2 hd' e
          have a2 := (hx ⟨7, by decide⟩).1
          simp only [S43.proj, S43.Stmt.varOf, List.getD_cons_zero, List.getD_cons_succ] at a1 a2
          change _ < ((lget bx.lo 7 : ℕ) : ℝ) / 2 ^ S43.P at hr
          linarith
    · subst e3
      cases e : hget bx.hi (vfK st) with
      | none => rw [e] at h3; simp at h3
      | some hf' =>
        rw [e] at h3
        simp only [Nat.blt_eq] at h3
        have hdf : w.d ≤ w.f := by simpa [S43.subcase] using hs
        have hr : ((hf' : ℕ) : ℝ) / 2 ^ S43.P < ((lget bx.lo 2 : ℕ) : ℝ) / 2 ^ S43.P :=
          div_lt_div_of_pos_right (by exact_mod_cast h3) hp
        cases st
        · change InBoxK bx (S43.proj .reg 3 w) at hx
          have a1 := (hx ⟨5, by decide⟩).2 hf' e
          have a2 := (hx ⟨2, by decide⟩).1
          simp only [S43.proj, S43.Stmt.varOf, List.getD_cons_zero, List.getD_cons_succ] at a1 a2
          linarith
        · change InBoxK bx (S43.proj .st 3 w) at hx
          have a1 := (hx ⟨7, by decide⟩).2 hf' e
          have a2 := (hx ⟨2, by decide⟩).1
          simp only [S43.proj, S43.Stmt.varOf, List.getD_cons_zero, List.getD_cons_succ] at a1 a2
          linarith
  · -- ok
    obtain ⟨sp, hsp, L, hL, ks, sk, hks, hsk, hYk, hmf, hbox⟩ :=
      checkRecordK_ok hf2 hrho hρ0 hρ1 hmono hglue hsize hlen hv
    have hf2' : fval = 2 → famOf st = .st := fun e => by rw [hf2 e]; rfl
    refine ⟨sp, hsp, L, hL, ?_⟩
    obtain ⟨ω, hω⟩ := hbox _ hx
    revert hf2' hω hks hsk hYk hmf hd
    generalize famOf st = F
    intro hd hks hsk hYk hmf hf2' hω
    by_cases h2 : fval = 2
    · subst h2
      obtain rfl := hf2' rfl
      rw [S43.embed_proj2] at hω
      have hdf : w.d ≤ w.f := by simpa [S43.subcase] using hs
      have hb := S43.Stmt.vset_bump hρ0 hρ1 (t := w.f - w.d) .f (Or.inr rfl) (hmf rfl) (fun e => by cases e)
        (fun e => by cases e.1) (by linarith) hω
      have hw : S43.Stmt.bump .f (w.f - w.d) { w with f := w.d } = w := by
        cases w; simp only [S43.Stmt.bump]; congr 1; ring
      rw [hw] at hb
      exact S43.Stmt.bridge hks hsk hb (S43.kScond_all hYk hs)
    · have huv : F = .reg → w.u = 0 ∧ w.v = 0 := fun e => by subst e; exact hd.2.2.2.2.2.2.2.2
      rw [S43.embed_proj h2 w huv] at hω
      exact S43.Stmt.bridge hks hsk hω (S43.kScond_all hYk hs)

end S43K

end
