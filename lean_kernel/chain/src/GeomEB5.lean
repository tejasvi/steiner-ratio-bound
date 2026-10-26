module

public import GeomEB4

@[expose] public section

/-! # K1 function layer, part 5: the explicit networks and max-distances

Mirrors lean/'s `enc_smt3n` (star at the Fermat point, or the path through a terminal = the star centred
there), `enc_net4n` (here: `minHi` over five explicit candidate networks) and `enc_maxdist`. Points within
2^135 (configuration points; witness points are within 2^121). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-! ## Star -/

theorem eb_star3 {a b c X : PK} {za zb zc zX : ℂ} (ha : PB 135 a za) (hb : PB 135 b zb) (hc : PB 135 c zc)
    (hX : PB 135 X zX) : EB 181 (star3 a b c X) (S43.Stmt.starLen za zb zc zX) := by
  unfold star3 S43.Stmt.starLen
  have d1 := eb_dist ha hX (by norm_num) (by norm_num)
  have d2 := eb_dist hb hX (by norm_num) (by norm_num)
  have d3 := eb_dist hc hX (by norm_num) (by norm_num)
  exact eb_add (eb_add d1 d2 (by norm_num)) (d3.mono (by norm_num)) (by norm_num)

/-- the Steiner point of `smt3K` (the terminal at a vertex whose angle is not certainly <= 120 degrees, else the
per-vertex Fermat point); lean/'s `smt3Pt` with `fermatV` in place of `fermatW` -/
noncomputable def smt3PtK (a b c : PK) (za zb zc : ℂ) : ℂ :=
  if !angleLe120 a b c then zb else if !angleLe120 b c a then zc else if !angleLe120 c a b then za
  else realPtK (fermatV a b c)

theorem eb_smt3K {a b c : PK} {za zb zc : ℂ} (ha : PB 135 a za) (hb : PB 135 b zb) (hc : PB 135 c zc) :
    EB 181 (smt3K a b c) (S43.Stmt.starLen za zb zc (smt3PtK a b c za zb zc)) := by
  have dab := eb_dist ha hb (by norm_num) (by norm_num)
  have dbc := eb_dist hb hc (by norm_num) (by norm_num)
  have dca := eb_dist hc ha (by norm_num) (by norm_num)
  have hX := (pb_isW (isW_fermatV a b c)).mono (show 121 ≤ 135 by norm_num)
  unfold smt3K smt3b smt3c smt3PtK
  cases h1 : angleLe120 a b c
  · rw [Bool.cond_false]
    simp only [Bool.not_false, ite_true]
    exact ((eb_add dab dbc (by norm_num)).mono (by norm_num)).congr
      (by unfold S43.Stmt.starLen S43.Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev zc zb]; ring)
  · rw [Bool.cond_true]
    cases h2 : angleLe120 b c a
    · rw [Bool.cond_false]
      simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
      exact ((eb_add dbc dca (by norm_num)).mono (by norm_num)).congr
        (by unfold S43.Stmt.starLen S43.Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev za zc]; ring)
    · rw [Bool.cond_true]
      cases h3 : angleLe120 c a b
      · rw [Bool.cond_false]
        simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
        exact ((eb_add dca dab (by norm_num)).mono (by norm_num)).congr
          (by unfold S43.Stmt.starLen S43.Stmt.dist; rw [sub_self, norm_zero, norm_sub_rev zb za]; ring)
      · rw [Bool.cond_true]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        exact eb_star3 ha hb hc hX

/-! ## The five pair candidates -/

theorem eb_pair4XY {p1 p2 p3 p4 X Y : PK} {z1 z2 z3 z4 zX zY : ℂ} (h1 : PB 135 p1 z1) (h2 : PB 135 p2 z2)
    (h3 : PB 135 p3 z3) (h4 : PB 135 p4 z4) (hX : PB 135 X zX) (hY : PB 135 Y zY) :
    EB 183 (pair4XY p1 p2 p3 p4 (X, Y)) (S43.Stmt.pairLen z1 z2 z3 z4 zX zY) := by
  unfold pair4XY S43.Stmt.pairLen
  have d1 := eb_dist h1 hX (by norm_num) (by norm_num)
  have d2 := eb_dist h2 hX (by norm_num) (by norm_num)
  have d3 := eb_dist hX hY (by norm_num) (by norm_num)
  have d4 := eb_dist h3 hY (by norm_num) (by norm_num)
  have d5 := eb_dist h4 hY (by norm_num) (by norm_num)
  have s2 := eb_add d1 d2 (by norm_num)
  have s3 := eb_add s2 (d3.mono (by norm_num)) (by norm_num)
  have s4 := eb_add s3 (d4.mono (by norm_num)) (by norm_num)
  exact eb_add s4 (d5.mono (by norm_num)) (by norm_num)

theorem minHi_cases (a b : DN) : minHi a b = a ∨ minHi a b = b := by
  unfold minHi; cases Nat.ble a.hi b.hi
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- one candidate network at witness points `XY` (both `IsW`) -/
theorem eb_cand {p1 p2 p3 p4 : PK} {z1 z2 z3 z4 : ℂ} (h1 : PB 135 p1 z1) (h2 : PB 135 p2 z2) (h3 : PB 135 p3 z3)
    (h4 : PB 135 p4 z4) {XY : PK × PK} (hw : IsW2 XY) :
    ∃ x y : ℂ, EB 183 (pair4XY p1 p2 p3 p4 XY) (S43.Stmt.pairLen z1 z2 z3 z4 x y) := by
  obtain ⟨X, Y⟩ := XY
  exact ⟨_, _, eb_pair4XY h1 h2 h3 h4 ((pb_isW hw.1).mono (by norm_num)) ((pb_isW hw.2).mono (by norm_num))⟩

theorem isW2_mk {a b : PK} (ha : IsW a) (hb : IsW b) : IsW2 (a, b) := ⟨ha, hb⟩

theorem eb_minHi_ex {a b : DN} {P : DN → Prop} (ha : P a) (hb : P b) : P (minHi a b) := by
  rcases minHi_cases a b with h | h <;> rw [h] <;> assumption

/-- pair4K: the selected candidate's whole interval encloses `pairLen` at that candidate's witness points -/
theorem eb_pair4K {p1 p2 p3 p4 : PK} {z1 z2 z3 z4 : ℂ} (h1 : PB 135 p1 z1) (h2 : PB 135 p2 z2) (h3 : PB 135 p3 z3)
    (h4 : PB 135 p4 z4) : ∃ x y : ℂ, EB 183 (pair4K p1 p2 p3 p4) (S43.Stmt.pairLen z1 z2 z3 z4 x y) := by
  unfold pair4K
  refine eb_minHi_ex (P := fun r => ∃ x y : ℂ, EB 183 r (S43.Stmt.pairLen z1 z2 z3 z4 x y)) ?_ ?_
  · refine eb_minHi_ex (P := fun r => ∃ x y : ℂ, EB 183 r (S43.Stmt.pairLen z1 z2 z3 z4 x y)) ?_ ?_
    · refine eb_minHi_ex (P := fun r => ∃ x y : ℂ, EB 183 r (S43.Stmt.pairLen z1 z2 z3 z4 x y)) ?_ ?_
      · refine eb_minHi_ex (P := fun r => ∃ x y : ℂ, EB 183 r (S43.Stmt.pairLen z1 z2 z3 z4 x y)) ?_ ?_
        · exact eb_cand h1 h2 h3 h4 (isW2_melzakV p1 p2 p3 p4)
        · exact eb_cand h1 h2 h3 h4 (isW2_mk (isW_cornerW p1) (isW_fermatR p1 p3 p4))
      · exact eb_cand h1 h2 h3 h4 (isW2_mk (isW_cornerW p2) (isW_fermatR p2 p3 p4))
    · exact eb_cand h1 h2 h3 h4 (isW2_mk (isW_fermatR p1 p2 p3) (isW_cornerW p3))
  · exact eb_cand h1 h2 h3 h4 (isW2_mk (isW_fermatR p1 p2 p4) (isW_cornerW p4))

/-! ## Max-distances (lean/'s `maxdist`, a left fold of `max` from 0) -/

theorem maxdist2 (zw za zb : ℂ) :
    S43.Stmt.maxdist zw [za, zb] = max (S43.Stmt.dist zw za) (S43.Stmt.dist zw zb) := by
  simp only [S43.Stmt.maxdist, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [max_eq_right (show (0 : ℝ) ≤ S43.Stmt.dist zw za from norm_nonneg _)]

theorem maxdist3 (zw za zb zc : ℂ) :
    S43.Stmt.maxdist zw [za, zb, zc] = max (S43.Stmt.maxdist zw [za, zb]) (S43.Stmt.dist zw zc) := by
  simp only [S43.Stmt.maxdist, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

theorem maxdist4 (zw za zb zc zd : ℂ) :
    S43.Stmt.maxdist zw [za, zb, zc, zd] = max (S43.Stmt.maxdist zw [za, zb, zc]) (S43.Stmt.dist zw zd) := by
  simp only [S43.Stmt.maxdist, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

theorem eb_maxd2 {w a b : PK} {zw za zb : ℂ} (hw : PB 135 w zw) (ha : PB 135 a za) (hb : PB 135 b zb) :
    EB 179 (maxd2 w a b) (S43.Stmt.maxdist zw [za, zb]) := by
  rw [maxdist2]; unfold maxd2
  exact eb_max (eb_dist hw ha (by norm_num) (by norm_num)) (eb_dist hw hb (by norm_num) (by norm_num))

theorem eb_maxd3 {w a b c : PK} {zw za zb zc : ℂ} (hw : PB 135 w zw) (ha : PB 135 a za) (hb : PB 135 b zb)
    (hc : PB 135 c zc) : EB 179 (maxd3 w a b c) (S43.Stmt.maxdist zw [za, zb, zc]) := by
  rw [maxdist3]; unfold maxd3
  exact eb_max (eb_maxd2 hw ha hb) (eb_dist hw hc (by norm_num) (by norm_num))

theorem eb_maxd4 {w a b c d : PK} {zw za zb zc zd : ℂ} (hw : PB 135 w zw) (ha : PB 135 a za) (hb : PB 135 b zb)
    (hc : PB 135 c zc) (hd : PB 135 d zd) : EB 179 (maxd4 w a b c d) (S43.Stmt.maxdist zw [za, zb, zc, zd]) := by
  rw [maxdist4]; unfold maxd4
  exact eb_max (eb_maxd3 hw ha hb hc) (eb_dist hw hd (by norm_num) (by norm_num))

end S43K

end
