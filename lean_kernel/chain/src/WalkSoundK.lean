module

public import RecordK
public import S43Walk.WalkK2
public import S43.Sound.Case

@[expose] public section

/-! # K3: the walk covers the case domain, unit claims transfer coverage, and the case theorem
(replaces lean/'s skeleton/shard decomposition; same conclusion `CaseOK` as its `case_good`)

`walkFold` (WalkK2) replays lean/'s DFS over the merged code stream with explicit skeleton/job stacks. Invariant `Cov G st`:
every point of [0, ∞)^nb satisfies `G` or lies in a box on the stacks. A split replaces a box by its two halves (which
cover it, whatever the midpoint), `'z'` moves a box between the stacks, and a leaf pops a box whose record passes, so
`G` holds on it (K2). A data unit's claim (`UnitClaim`) therefore transfers coverage from its start stack to its end
stack; units chain by their stack literals, from the root box (which covers the domain) to the empty stack, which leaves
`G` everywhere: the case is `CaseOK`. -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-! ## Boxes of the walk (scale 2^-40) -/

/-- a point lies in a walk box -/
def InBoxS (b : BoxS) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, ((lget b.lo j : ℕ) : ℝ) / 2 ^ 40 ≤ x j ∧ ∀ h : ℕ, hget b.hi j = some h → x j ≤ (h : ℝ) / 2 ^ 40

theorem lget_setN : ∀ (l : List ℕ) (k j v : ℕ), lget (setN l k v) j = if j = k ∧ k < l.length then v else lget l j
  | [], _, _, _ => by simp [setN, lget]
  | x :: xs, 0, j, v => by
    cases j <;> simp [setN, lget]
  | x :: xs, k + 1, j, v => by
    cases j with
    | zero => simp [setN, lget]
    | succ j =>
      have := lget_setN xs k j v
      simp only [lget, setN, List.getD_cons_succ, List.length_cons] at this ⊢
      rw [this]; simp

theorem hget_setO : ∀ (l : List (Option ℕ)) (k j : ℕ) (v : Option ℕ),
    hget (setO l k v) j = if j = k ∧ k < l.length then v else hget l j
  | [], _, _, _ => by simp [setO, hget]
  | x :: xs, 0, j, v => by
    cases j <;> simp [setO, hget]
  | x :: xs, k + 1, j, v => by
    cases j with
    | zero => simp [setO, hget]
    | succ j =>
      have := hget_setO xs k j v
      simp only [hget, setO, List.getD_cons_succ, List.length_cons] at this ⊢
      rw [this]; simp

/-- the two halves cover the box, for any midpoint -/
theorem cover_halves {b : BoxS} {n : ℕ} {x : Fin n → ℝ} (k m : ℕ) (h : InBoxS b x) :
    InBoxS (halfLo b k m) x ∨ InBoxS (halfHi b k m) x := by
  by_cases hx : ∀ j : Fin n, (j : ℕ) = k → x j ≤ (m : ℝ) / 2 ^ 40
  · left
    intro j
    refine ⟨(h j).1, fun hh e => ?_⟩
    simp only [halfLo, hget_setO] at e
    split_ifs at e with c
    · simp only [Option.some.injEq] at e; subst e; exact hx j c.1
    · exact (h j).2 hh e
  · right
    push Not at hx
    obtain ⟨j0, hj0, hlt⟩ := hx
    intro j
    refine ⟨?_, fun hh e => (h j).2 hh (by simpa [halfHi] using e)⟩
    simp only [halfHi, lget_setN]
    split_ifs with c
    · have : j = j0 := Fin.ext (by rw [c.1, hj0])
      subst this; exact hlt.le
    · exact (h j).1

/-! ## Coverage and its transfer -/

/-- every point of the domain satisfies `G` or lies in a box of the stacks -/
def Cov {n : ℕ} (G : (Fin n → ℝ) → Prop) (st : WSt) : Prop :=
  ∀ x : Fin n → ℝ, (∀ j, 0 ≤ x j) → G x ∨ ∃ b ∈ st.sk ++ st.js, InBoxS b x

/-- `G` holds on the box of every passing record -/
def LeafGood (st : Bool) (fval nb : ℕ) (G : (Fin nb → ℝ) → Prop) : Prop :=
  ∀ r : RecK, recOK st fval nb r → ∀ x : Fin nb → ℝ, InBoxS ⟨r.lo, r.hi⟩ x → G x

/-- a unit's semantics: coverage from stack `S` to stack `T` -/
def Transfer (st : Bool) (fval nb : ℕ) (S T : List BoxS) : Prop :=
  ∀ G : (Fin nb → ℝ) → Prop, LeafGood st fval nb G → Cov G ⟨S, []⟩ → Cov G ⟨T, []⟩

theorem ForallR_mem {P : RecK → Prop} : ∀ {l : List RecK}, ForallR P l → ∀ r ∈ l, P r
  | [], _, r, hr => by simp at hr
  | a :: l, h, r, hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.1
    · exact ForallR_mem h.2 r hr

/-- the fold preserves coverage, given that every record it ends with passes -/
theorem walkFold_cov {nb : ℕ} {st : Bool} {fval : ℕ} {G : (Fin nb → ℝ) → Prop} (hG : LeafGood st fval nb G) :
    ∀ (cs : List ℕ) (s : WSt) (acc : List RecK) (s' : WSt) (acc' : List RecK),
      walkFold nb cs s acc = some (s', acc') → (∀ r ∈ acc', recOK st fval nb r) →
      (∀ r ∈ acc, r ∈ acc') ∧ (Cov G s → Cov G s')
  | [], s, acc, s', acc', h, _ => by
    simp only [walkFold, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun r hr => hr, id⟩
  | c :: cs, ⟨b :: sk, []⟩, acc, s', acc', h, hrec => by
    simp only [walkFold] at h
    cases hz : Nat.beq c 122
    · rw [hz, Bool.cond_false] at h
      cases hs : isSplit nb c
      · rw [hs, Bool.cond_false] at h; exact absurd h (by simp)
      · rw [hs, Bool.cond_true] at h
        split at h
        · exact absurd h (by simp)
        · rename_i m _
          obtain ⟨hsub, hcov⟩ := walkFold_cov hG cs _ acc s' acc' h hrec
          refine ⟨hsub, fun hc => hcov (fun x hx => ?_)⟩
          rcases hc x hx with hg | ⟨b', hb', hin⟩
          · exact Or.inl hg
          · right
            simp only [List.append_nil, List.mem_cons] at hb' ⊢
            rcases hb' with rfl | hb'
            · rcases cover_halves (Nat.sub c 33) m hin with h1 | h1
              · exact ⟨_, Or.inl rfl, h1⟩
              · exact ⟨_, Or.inr (Or.inl rfl), h1⟩
            · exact ⟨b', Or.inr (Or.inr hb'), hin⟩
    · rw [hz, Bool.cond_true] at h
      obtain ⟨hsub, hcov⟩ := walkFold_cov hG cs _ acc s' acc' h hrec
      refine ⟨hsub, fun hc => hcov (fun x hx => ?_)⟩
      rcases hc x hx with hg | ⟨b', hb', hin⟩
      · exact Or.inl hg
      · right
        simp only [List.append_nil, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hin⟩
        · exact ⟨b', List.mem_append_left _ hb', hin⟩
  | c :: cs, ⟨sk, b :: js⟩, acc, s', acc', h, hrec => by
    cases sk <;> (unfold walkFold at h; try simp only at h)
    all_goals
      cases hs : isSplit nb c
      · rw [hs, Bool.cond_false] at h
        cases hl : isLeafC c
        · rw [hl, Bool.cond_false] at h; exact absurd h (by simp)
        · rw [hl, Bool.cond_true] at h
          split at h
          · rename_i d1 d2 cs'
            cases hd : (isDigit d1 && isDigit d2)
            · rw [hd, Bool.cond_false] at h; exact absurd h (by simp)
            · rw [hd, Bool.cond_true] at h
              obtain ⟨hsub, hcov⟩ := walkFold_cov hG cs' _ _ s' acc' h hrec
              refine ⟨fun r hr => hsub r (List.mem_cons_of_mem _ hr), fun hc => hcov (fun x hx => ?_)⟩
              rcases hc x hx with hg | ⟨b', hb', hin⟩
              · exact Or.inl hg
              · rcases List.mem_append.1 hb' with hb' | hb'
                · exact Or.inr ⟨b', List.mem_append_left _ hb', hin⟩
                · rcases List.mem_cons.1 hb' with rfl | hb'
                  · left
                    have hr := hrec _ (hsub _ List.mem_cons_self)
                    exact hG _ hr x hin
                  · exact Or.inr ⟨b', List.mem_append_right _ hb', hin⟩
          · exact absurd h (by simp)
      · rw [hs, Bool.cond_true] at h
        split at h
        · exact absurd h (by simp)
        · rename_i m _
          obtain ⟨hsub, hcov⟩ := walkFold_cov hG cs _ acc s' acc' h hrec
          refine ⟨hsub, fun hc => hcov (fun x hx => ?_)⟩
          rcases hc x hx with hg | ⟨b', hb', hin⟩
          · exact Or.inl hg
          · right
            rcases List.mem_append.1 hb' with hb' | hb'
            · exact ⟨b', List.mem_append_left _ hb', hin⟩
            · rcases List.mem_cons.1 hb' with rfl | hb'
              · rcases cover_halves (Nat.sub c 33) m hin with h1 | h1
                · exact ⟨_, List.mem_append_right _ List.mem_cons_self, h1⟩
                · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), h1⟩
              · exact ⟨b', List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb')), hin⟩
  | _ :: _, ⟨[], []⟩, _, _, _, h, _ => by simp [walkFold] at h

theorem unit_transfer {st : Bool} {fval nb : ℕ} {S T : List BoxS} (h : UnitClaim st fval nb S T) :
    Transfer st fval nb S T := by
  intro G hG hS
  obtain ⟨ws, n, recsRev, hw, hall⟩ := h
  unfold unitWalkOK at hw
  split at hw
  · rename_i s' acc hfold
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact (walkFold_cov hG _ _ _ _ _ hfold (ForallR_mem hall)).2 hS
  · exact absurd hw (by simp)

theorem transfer_refl (st : Bool) (fval nb : ℕ) (S : List BoxS) : Transfer st fval nb S S := fun _ _ h => h

theorem transfer_trans {st : Bool} {fval nb : ℕ} {S T U : List BoxS} (h1 : Transfer st fval nb S T)
    (h2 : Transfer st fval nb T U) : Transfer st fval nb S U := fun G hG hS => h2 G hG (h1 G hG hS)

/-! ## K4: the case theorem (same conclusion as lean/'s `case_good`) -/

theorem lget_up60 : ∀ (l : List ℕ) (j : ℕ), lget (up60 l) j = lget l j * 2 ^ 60
  | [], j => by simp [up60, lget]
  | x :: xs, 0 => by simp [up60, lget, Nat.shiftLeft_eq]
  | x :: xs, j + 1 => by
    have := lget_up60 xs j
    simp only [lget, up60, List.getD_cons_succ] at this ⊢; exact this

theorem hget_up60o : ∀ (l : List (Option ℕ)) (j : ℕ), hget (up60o l) j = (hget l j).map (· * 2 ^ 60)
  | [], j => by simp [up60o, hget]
  | none :: xs, 0 => by simp [up60o, hget]
  | some x :: xs, 0 => by simp [up60o, hget, Nat.shiftLeft_eq]
  | none :: xs, j + 1 => by
    have := hget_up60o xs j
    simp only [hget, up60o, List.getD_cons_succ] at this ⊢; exact this
  | some x :: xs, j + 1 => by
    have := hget_up60o xs j
    simp only [hget, up60o, List.getD_cons_succ] at this ⊢; exact this

theorem scale60 (a : ℕ) : (((a * 2 ^ 60 : ℕ) : ℝ) / 2 ^ S43.P) = (a : ℝ) / 2 ^ 40 := by
  rw [show S43.P = 100 from rfl]; push_cast
  rw [show (2 : ℝ) ^ 100 = 2 ^ 60 * 2 ^ 40 by norm_num]
  field_simp
  norm_num

/-- a walk box (scale 2^-40) and its lifted checker box (scale 2^-100) contain the same points -/
theorem inBoxS_up60 (b : BoxS) {n : ℕ} (x : Fin n → ℝ) : InBoxS b x ↔ InBoxK ⟨up60 b.lo, up60o b.hi⟩ x := by
  unfold InBoxS InBoxK
  simp only [lget_up60, hget_up60o, scale60]
  constructor
  · intro h j
    refine ⟨(h j).1, fun hh e => ?_⟩
    cases e' : hget b.hi j with
    | none => rw [e'] at e; simp at e
    | some h0 =>
      rw [e'] at e; simp only [Option.map_some, Option.some.injEq] at e; subst e
      rw [scale60]; exact (h j).2 h0 e'
  · intro h j
    refine ⟨(h j).1, fun hh e => ?_⟩
    have := (h j).2 (hh * 2 ^ 60) (by rw [e]; rfl)
    rwa [scale60] at this

/-- the case property (the `G` of lean/'s `case_good`) -/
def caseG (st : Bool) (fval : ℕ) (ρ : ℝ) (x : Fin (S43.Stmt.nbOf (famOf st) fval) → ℝ) : Prop :=
  ∀ w, (∀ j : Fin (S43.Stmt.nbOf (famOf st) fval), x j = S43.Stmt.varOf (famOf st) w j) → S43.Good (famOf st) fval ρ w

theorem leafGood_case {st : Bool} {fval : ℕ}
    (hcase : (st = true ∧ (fval = 1 ∨ fval = 2)) ∨ (st = false ∧ (fval = 1 ∨ fval = 3))) {ρ : ℝ}
    (hrho : (toDI RHO).Enc ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : S43.MonoData (famOf st) fval)
    (hglue : ∀ i, 1 ≤ i → i ≤ nSplits st → toSplit (splitK st i) = (S43.Stmt.splits (famOf st))[i - 1]!)
    (hsize : (S43.Stmt.splits (famOf st)).size = nSplits st)
    (hlen : ∀ i, 1 ≤ i → i ≤ nSplits st → (splitK st i).ta.length ≤ 40 ∧ (splitK st i).sm.length ≤ 40) :
    LeafGood st fval (S43.Stmt.nbOf (famOf st) fval) (caseG st fval ρ) := by
  intro r hr x hx w hw
  have hgood := checkRecordK_good hcase hrho hρ0 hρ1 hmono hglue hsize hlen hr w
  apply hgood
  have e : x = S43.proj (famOf st) fval w := funext hw
  rw [← e]; exact (inBoxS_up60 _ x).1 hx

/-- K4: a case whose walk transfers coverage from the root stack to the empty stack is `CaseOK` -/
theorem case_goodK {st : Bool} {fval : ℕ}
    (hcase : (st = true ∧ (fval = 1 ∨ fval = 2)) ∨ (st = false ∧ (fval = 1 ∨ fval = 3))) {ρ : ℝ}
    (hrho : (toDI RHO).Enc ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hmono : S43.MonoData (famOf st) fval)
    (hglue : ∀ i, 1 ≤ i → i ≤ nSplits st → toSplit (splitK st i) = (S43.Stmt.splits (famOf st))[i - 1]!)
    (hsize : (S43.Stmt.splits (famOf st)).size = nSplits st)
    (hlen : ∀ i, 1 ≤ i → i ≤ nSplits st → (splitK st i).ta.length ≤ 40 ∧ (splitK st i).sm.length ≤ 40)
    {rootSk : List BoxS}
    (hroot : ∀ x : Fin (S43.Stmt.nbOf (famOf st) fval) → ℝ, (∀ j, 0 ≤ x j) → ∃ b ∈ rootSk, InBoxS b x)
    (hT : Transfer st fval (S43.Stmt.nbOf (famOf st) fval) rootSk []) : S43.CaseOK (famOf st) fval ρ := by
  have hG := leafGood_case hcase hrho hρ0 hρ1 hmono hglue hsize hlen
  have hcov : Cov (caseG st fval ρ) ⟨rootSk, []⟩ := fun x hx => Or.inr (by simpa using hroot x hx)
  have hend := hT _ hG hcov
  intro w hd hs
  have hx : ∀ j, 0 ≤ (S43.proj (famOf st) fval w) j := fun j => S43.varOf_nonneg hd j
  rcases hend _ hx with hg | ⟨b, hb, _⟩
  · exact hg w (fun j => rfl) hd hs
  · simp at hb

/-- the root box `[0, ∞)^n` covers the domain -/
theorem root_cover (n : ℕ) (x : Fin n → ℝ) (hx : ∀ j, 0 ≤ x j) :
    InBoxS ⟨List.replicate n 0, List.replicate n none⟩ x := by
  intro j
  refine ⟨?_, fun h e => ?_⟩
  · have : lget (List.replicate n 0) j = 0 := by
      unfold lget; rw [List.getD_eq_getElem?_getD]; simp
    rw [this]; simpa using hx j
  · have : hget (List.replicate n none) j = none := by
      unfold hget; rw [List.getD_eq_getElem?_getD]; simp
    rw [this] at e; exact absurd e (by simp)

end S43K

#print axioms S43K.case_goodK
#print axioms S43K.unit_transfer

end
