module

public import S43.Sound.Enc

@[expose] public section

/-! # Soundness of the vertex evaluation

`evalVertexN_sound`: if the checker accepts a vertex whose variable values enclose `w`, then the term kinds and the S+
kind of the split are defined and `w` has the network property `vset` for an explicit witness `ω` (the Steiner points
used by the checker, as exact dyadic points). -/

namespace S43

attribute [local irreducible] P

open DI

/-! ## Explicit points -/

/-- the real point of an interval point (lower ends) -/
noncomputable def realPt (X : Pt) : ℂ := ⟨(X.1.lo : ℝ) / 2 ^ P, (X.2.lo : ℝ) / 2 ^ P⟩

def Exact (X : Pt) : Prop := X.1.lo = X.1.hi ∧ X.2.lo = X.2.hi

theorem enc_realPt {X : Pt} (h : Exact X) : PtEnc X (realPt X) := by
  have hp := pow_P_pos
  have e : ∀ m : ℤ, (2 : ℝ) ^ P * ((m : ℝ) / 2 ^ P) = m := fun m => by field_simp
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [realPt, e] <;> simp [h.1, h.2]

theorem exact_fermatW (a b c : Pt) : Exact (fermatW a b c) := ⟨rfl, rfl⟩

theorem exact_net4W (p1 p2 p3 p4 : Pt) : Exact (net4W p1 p2 p3 p4).1 ∧ Exact (net4W p1 p2 p3 p4).2 :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- the Steiner point of the 3-point bound `smt3n` -/
noncomputable def smt3Pt (a b c : Pt) (za zb zc : ℂ) : ℂ :=
  if !angleLe120 a b c then zb else if !angleLe120 b c a then zc else if !angleLe120 c a b then za
  else realPt (fermatW a b c)

theorem enc_smt3n {a b c : Pt} {za zb zc : ℂ} (ha : PtEnc a za) (hb : PtEnc b zb) (hc : PtEnc c zc) :
    (smt3n a b c).Enc (Stmt.starLen za zb zc (smt3Pt a b c za zb zc)) := by
  have dab := enc_dist ha hb; have dbc := enc_dist hb hc; have dca := enc_dist hc ha
  unfold smt3n smt3Pt
  split_ifs
  · exact Enc.congr (enc_add dab dbc) (by unfold Stmt.starLen Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev zc zb]; ring)
  · exact Enc.congr (enc_add dbc dca) (by unfold Stmt.starLen Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev za zc]; ring)
  · exact Enc.congr (enc_add dca dab) (by unfold Stmt.starLen Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev zb za]; ring)
  · have hX := enc_realPt (exact_fermatW a b c)
    exact enc_add (enc_add (enc_dist ha hX) (enc_dist hb hX)) (enc_dist hc hX)

theorem enc_net4n {p1 p2 p3 p4 : Pt} {z1 z2 z3 z4 : ℂ} (h1 : PtEnc p1 z1) (h2 : PtEnc p2 z2) (h3 : PtEnc p3 z3)
    (h4 : PtEnc p4 z4) :
    (net4n p1 p2 p3 p4).Enc
      (Stmt.pairLen z1 z2 z3 z4 (realPt (net4W p1 p2 p3 p4).1) (realPt (net4W p1 p2 p3 p4).2)) := by
  have hX := enc_realPt (exact_net4W p1 p2 p3 p4).1
  have hY := enc_realPt (exact_net4W p1 p2 p3 p4).2
  exact enc_add (enc_add (enc_add (enc_add (enc_dist h1 hX) (enc_dist h2 hX)) (enc_dist hX hY)) (enc_dist h3 hY))
    (enc_dist h4 hY)

/-! ## maxdist -/

theorem enc_maxdist_fold (P : Array Pt) (wi : ℕ) (zw : ℂ) (hw : PtEnc P[wi]! zw) :
    ∀ (l : List ℕ) (zs : List ℂ) (acc : DI) (accR : ℝ), acc.Enc accR → List.Forall₂ (fun i z => PtEnc P[i]! z) l zs →
      (l.foldl (fun z y => z.max (S43.dist P[wi]! P[y]!)) acc).Enc ((zs.map (Stmt.dist zw)).foldl max accR) := by
  intro l
  induction l with
  | nil => intro zs acc accR ha h; cases h; simpa using ha
  | cons i l ih =>
    intro zs acc accR ha h
    cases h with
    | cons hi hl =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih _ _ _ (enc_max ha (enc_dist hw hi)) hl

theorem enc_maxdist (P : Array Pt) (wi : ℕ) (zw : ℂ) (hw : PtEnc P[wi]! zw) (l : List ℕ) (zs : List ℂ)
    (hl : l ≠ []) (h : List.Forall₂ (fun i z => PtEnc P[i]! z) l zs) :
    (S43.maxdist P wi l).Enc (Stmt.maxdist zw zs) := by
  cases h with
  | nil => exact absurd rfl hl
  | @cons a b _ _ hi hr =>
    simp only [S43.maxdist, Stmt.maxdist, List.map_cons, List.foldl_cons]
    have h0 : (0 : ℝ) ≤ Stmt.dist zw b := norm_nonneg _
    rw [max_eq_right h0]
    exact enc_maxdist_fold P wi zw hw _ _ _ _ (enc_dist hw hi) hr

/-! ## Lemma X2's condition -/

theorem x2Cond_sound {I : Ids} {V : Array DI} {w : Stmt.Vars} (hc : (V[I.vc]!).Enc w.c) (he : (V[I.ve]!).Enc w.e)
    (hf : (V[I.vf]!).Enc w.f) (h : x2Cond I V (TWO_OVER_SQ3_M1 * V[I.vc]!) = true) : Stmt.cond5 w := by
  have hkc : (TWO_OVER_SQ3_M1 * V[I.vc]!).Enc ((2 / √3 - 1) * w.c) := enc_mul enc_two_over hc
  unfold x2Cond at h
  simp only at h
  split_ifs at h with h1 h2
  · left; exact ltc_sound he hkc h1
  · right
    have h2' : (V[I.ve]!).ltc V[I.vc]! = true := by simpa using h2
    refine ⟨ltc_sound he hc h2', ?_⟩
    have ht := enc_sqrt (enc_add (enc_add (enc_sq he) (enc_mul he hf)) (enc_sq hf))
    have hphi := enc_sub (enc_sub (enc_add (enc_add hc he) hf) ht) (enc_half (enc_mul (enc_add hc he) enc_SQ3))
    have := pos_sound hphi h
    convert this using 1; ring

/-! ## The configuration points by name -/

theorem PEnc.nodes {F : Stmt.Fam} {P : Array Pt} {w : Stmt.Vars} (h : PEnc F P w) :
    let I := Stmt.ids F; let p := Stmt.pts w
    PtEnc P[I.nA]! p.A ∧ PtEnc P[I.nB]! p.B ∧ PtEnc P[I.nD]! p.D ∧ PtEnc P[I.nP]! p.P ∧ PtEnc P[I.nQ]! p.Q ∧
      PtEnc P[I.nR]! p.R ∧ PtEnc P[I.nS]! p.s ∧ PtEnc P[I.nr]! p.r ∧
      (F = .st → PtEnc P[I.nU]! p.U ∧ PtEnc P[I.nV]! p.V) := by
  intro I p
  cases F
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h' => by cases h'⟩ <;>
    first
    | exact h 0 (by decide) | exact h 1 (by decide) | exact h 2 (by decide) | exact h 3 (by decide)
    | exact h 4 (by decide) | exact h 5 (by decide) | exact h 6 (by decide) | exact h 7 (by decide)
  · refine ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
      h 8 (by decide), h 9 (by decide), fun _ => ⟨h 3 (by decide), h 4 (by decide)⟩⟩

end S43

end
