module

public import Mathlib
public import S43Core.Interval

@[expose] public section

/-! # Soundness of the dyadic intervals

`I.Enc x`: the interval `I` encloses the real number `x`, i.e. `lo ≤ 2^P x ≤ hi`. Every operation of `S43Core.Interval` maps
enclosures to enclosures. -/

namespace S43

-- keep `P` (= 100) opaque in proofs: unfolding it makes tactics evaluate 2^100 by recursion
attribute [local irreducible] P

/-- the product of two real numbers in two intervals lies between the smallest and the largest corner product -/
theorem corner_bounds {a1 a2 b1 b2 X Y : ℝ} (hx1 : a1 ≤ X) (hx2 : X ≤ a2) (hy1 : b1 ≤ Y) (hy2 : Y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ X * Y ∧
    X * Y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  constructor
  · rcases le_total 0 Y with hY | hY
    · have : a1 * Y ≤ X * Y := by nlinarith
      rcases le_total 0 a1 with ha | ha
      · have : a1 * b1 ≤ a1 * Y := by nlinarith
        simp only [min_le_iff]; left; left; linarith
      · have : a1 * b2 ≤ a1 * Y := by nlinarith
        simp only [min_le_iff]; left; right; linarith
    · have : a2 * Y ≤ X * Y := by nlinarith
      rcases le_total 0 a2 with ha | ha
      · have : a2 * b1 ≤ a2 * Y := by nlinarith
        simp only [min_le_iff]; right; left; linarith
      · have : a2 * b2 ≤ a2 * Y := by nlinarith
        simp only [min_le_iff]; right; right; linarith
  · rcases le_total 0 Y with hY | hY
    · have : X * Y ≤ a2 * Y := by nlinarith
      rcases le_total 0 a2 with ha | ha
      · have : a2 * Y ≤ a2 * b2 := by nlinarith
        simp only [le_max_iff]; right; right; linarith
      · have : a2 * Y ≤ a2 * b1 := by nlinarith
        simp only [le_max_iff]; right; left; linarith
    · have : X * Y ≤ a1 * Y := by nlinarith
      rcases le_total 0 a1 with ha | ha
      · have : a1 * Y ≤ a1 * b2 := by nlinarith
        simp only [le_max_iff]; left; right; linarith
      · have : a1 * Y ≤ a1 * b1 := by nlinarith
        simp only [le_max_iff]; left; left; linarith

theorem imin_cast (a b : ℤ) : ((DI.imin a b : ℤ) : ℝ) = min (a : ℝ) b := by
  unfold DI.imin; split_ifs with h
  · rw [min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right (by exact_mod_cast (not_le.mp h).le)]

theorem imax_cast (a b : ℤ) : ((DI.imax a b : ℤ) : ℝ) = max (a : ℝ) b := by
  unfold DI.imax; split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (by exact_mod_cast (not_le.mp h).le)]

theorem two_pow_pos' (k : ℕ) : (0 : ℝ) < 2 ^ k := by positivity

/-- shift = floor division: `fl z k * 2^k ≤ z ≤ ce z k * 2^k` -/
theorem fl_le (z : ℤ) (k : ℕ) : ((DI.fl z k : ℤ) : ℝ) * 2 ^ k ≤ z := by
  have h : DI.fl z k = z / (2 ^ k : ℤ) := by simp [DI.fl, Int.shiftRight_eq_div_pow]
  rw [h]
  have hd : (0 : ℤ) < 2 ^ k := by positivity
  exact_mod_cast Int.ediv_mul_le z (ne_of_gt hd)

theorem le_ce (z : ℤ) (k : ℕ) : (z : ℝ) ≤ ((DI.ce z k : ℤ) : ℝ) * 2 ^ k := by
  have := fl_le (-z) k
  have h : DI.ce z k = -(DI.fl (-z) k) := by simp [DI.ce, DI.fl]
  rw [h]; push_cast at this ⊢; linarith

namespace DI

def Enc (I : DI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ 2 ^ P * x ∧ 2 ^ P * x ≤ (I.hi : ℝ)

theorem enc_add {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) : (a.add b).Enc (x + y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  refine ⟨?_, ?_⟩ <;> simp only [add] <;> push_cast <;> linarith

theorem enc_neg {a : DI} {x : ℝ} (ha : a.Enc x) : a.neg.Enc (-x) := by
  obtain ⟨h1, h2⟩ := ha
  refine ⟨?_, ?_⟩ <;> simp only [neg] <;> push_cast <;> linarith

theorem enc_sub {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) : (a.sub b).Enc (x - y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  refine ⟨?_, ?_⟩ <;> simp only [sub] <;> push_cast <;> linarith

theorem enc_nmul {a : DI} {x : ℝ} (k : ℕ) (ha : a.Enc x) : (a.nmul k).Enc (k * x) := by
  obtain ⟨h1, h2⟩ := ha
  have hk : (0 : ℝ) ≤ k := by positivity
  refine ⟨?_, ?_⟩ <;> simp only [nmul] <;> push_cast <;> nlinarith

theorem enc_half {a : DI} {x : ℝ} (ha : a.Enc x) : a.half.Enc (x / 2) := by
  obtain ⟨h1, h2⟩ := ha
  have f := fl_le a.lo 1; have c := le_ce a.hi 1
  refine ⟨?_, ?_⟩ <;> simp only [half] <;> linarith

theorem enc_mul {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) : (a.mul b).Enc (x * y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  obtain ⟨c1, c2⟩ := corner_bounds h1 h2 h3 h4
  have e : (2 ^ P * x) * (2 ^ P * y) = (2 ^ P * (x * y)) * 2 ^ P := by ring
  rw [e] at c1 c2
  have hp := two_pow_pos' P
  have f := fl_le (imin (imin (a.lo * b.lo) (a.lo * b.hi)) (imin (a.hi * b.lo) (a.hi * b.hi))) P
  have c := le_ce (imax (imax (a.lo * b.lo) (a.lo * b.hi)) (imax (a.hi * b.lo) (a.hi * b.hi))) P
  simp only [imin_cast, imax_cast, Int.cast_mul] at f c
  refine ⟨?_, ?_⟩
  · simp only [mul]
    have : ((fl (imin (imin (a.lo * b.lo) (a.lo * b.hi)) (imin (a.hi * b.lo) (a.hi * b.hi))) P : ℤ) : ℝ) * 2 ^ P
        ≤ (2 ^ P * (x * y)) * 2 ^ P := le_trans f c1
    exact le_of_mul_le_mul_right this hp
  · simp only [mul]
    have : (2 ^ P * (x * y)) * 2 ^ P
        ≤ ((ce (imax (imax (a.lo * b.lo) (a.lo * b.hi)) (imax (a.hi * b.lo) (a.hi * b.hi))) P : ℤ) : ℝ) * 2 ^ P :=
      le_trans c2 c
    exact le_of_mul_le_mul_right this hp

/-- `(m.toNat <<< P : ℝ) = m * 2^P` for `m ≥ 0` -/
theorem shift_cast {m : ℤ} (hm : 0 ≤ m) : (((m.toNat <<< P : ℕ)) : ℝ) = m * 2 ^ P := by
  rw [Nat.shiftLeft_eq]; push_cast
  rw [show ((m.toNat : ℕ) : ℝ) = (m : ℝ) by exact_mod_cast Int.toNat_of_nonneg hm]

theorem enc_sqrt {a : DI} {x : ℝ} (ha : a.Enc x) : a.sqrt.Enc (Real.sqrt x) := by
  obtain ⟨h1, h2⟩ := ha
  have hp := two_pow_pos' P
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  refine ⟨?_, ?_⟩
  · simp only [sqrt]
    split_ifs with hl
    · push_cast; positivity
    · have hl' : 0 < a.lo := lt_of_not_ge hl
      have hx : 0 < x := by
        have : (0 : ℝ) < a.lo := by exact_mod_cast hl'
        nlinarith
      have hsq := Nat.sqrt_le (a.lo.toNat <<< P)
      have hn := shift_cast hl'.le
      have key : ((Nat.sqrt (a.lo.toNat <<< P) : ℕ) : ℝ) ^ 2 ≤ (2 ^ P * Real.sqrt x) ^ 2 := by
        have e : (2 ^ P * Real.sqrt x) ^ 2 = 2 ^ P * (2 ^ P * x) := by
          rw [mul_pow, Real.sq_sqrt hx.le]; ring
        rw [e]
        have : ((Nat.sqrt (a.lo.toNat <<< P) * Nat.sqrt (a.lo.toNat <<< P) : ℕ) : ℝ) ≤ ((a.lo.toNat <<< P : ℕ) : ℝ) := by
          exact_mod_cast hsq
        rw [hn] at this; push_cast at this
        nlinarith
      have := (sq_le_sq₀ (by positivity) (by positivity)).mp key
      push_cast; exact this
  · simp only [sqrt]
    split_ifs with hh
    · -- hi ≤ 0 forces x ≤ 0, so sqrt x = 0
      have : x ≤ 0 := by
        have : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hh
        nlinarith
      rw [Real.sqrt_eq_zero'.mpr this]; simp
    · have hh' : 0 < a.hi := lt_of_not_ge hh
      have hlt := Nat.lt_succ_sqrt (a.hi.toNat <<< P)
      have hn := shift_cast hh'.le
      by_cases hx : x ≤ 0
      · rw [Real.sqrt_eq_zero'.mpr hx]; push_cast; nlinarith [Nat.zero_le (Nat.sqrt (a.hi.toNat <<< P))]
      · push_neg at hx
        have key : (2 ^ P * Real.sqrt x) ^ 2 < ((Nat.sqrt (a.hi.toNat <<< P) + 1 : ℕ) : ℝ) ^ 2 := by
          have e : (2 ^ P * Real.sqrt x) ^ 2 = 2 ^ P * (2 ^ P * x) := by
            rw [mul_pow, Real.sq_sqrt hx.le]; ring
          rw [e]
          have : ((a.hi.toNat <<< P : ℕ) : ℝ) < ((Nat.succ (Nat.sqrt (a.hi.toNat <<< P)) * Nat.succ (Nat.sqrt (a.hi.toNat <<< P)) : ℕ) : ℝ) := by
            exact_mod_cast hlt
          rw [hn] at this; push_cast at this ⊢
          have h3 : 2 ^ P * (2 ^ P * x) ≤ (a.hi : ℝ) * 2 ^ P := by nlinarith
          have h4 : ((Nat.sqrt (a.hi.toNat <<< P) : ℝ) + 1) ^ 2
              = ((Nat.sqrt (a.hi.toNat <<< P) : ℝ) + 1) * ((Nat.sqrt (a.hi.toNat <<< P) : ℝ) + 1) := by ring
          rw [h4]; linarith
        have := (sq_lt_sq₀ (by positivity) (by positivity)).mp key
        push_cast at this ⊢; linarith

end DI
end S43

end
