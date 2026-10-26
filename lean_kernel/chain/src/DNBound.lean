module

public import DNSim
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Ring.Abs

@[expose] public section

/-! # K1: static bounds give the no-truncation conditions

`BndD k a`: both endpoints of the biased interval `a` lie within `2^k` of the bias `B`. The lemmas below turn bounds on
the inputs of an op into (1) the no-truncation hypotheses of its simulation lemma in `DNSim` and (2) a bound on its
output. -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- `|x - B| < 2^k` for a biased endpoint `x` -/
def InR (k : Nat) (x : Nat) : Prop := B < x + 2 ^ k ∧ x < B + 2 ^ k

/-- both endpoints within `2^k` of the bias -/
def BndD (k : Nat) (a : DN) : Prop := InR k a.lo ∧ InR k a.hi

theorem InR.mono {k k' x : Nat} (h : InR k x) (hk : k ≤ k') : InR k' x := by
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  exact ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem BndD.mono {k k' : Nat} {a : DN} (h : BndD k a) (hk : k ≤ k') : BndD k' a :=
  ⟨h.1.mono hk, h.2.mono hk⟩

theorem pow_le_254 {k : Nat} (hk : k ≤ 254) : 2 ^ k ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) hk

theorem B_eq_4 : B = 4 * 2 ^ 254 := by rw [B_val]; norm_num

/-! ## add / sub -/

theorem add_ok {k : Nat} {a b : DN} (ha : BndD k a) (hb : BndD k b) (hk : k ≤ 254) :
    B ≤ a.lo + b.lo ∧ B ≤ a.hi + b.hi := by
  have h1 := pow_le_254 hk; have h2 := B_eq_4
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha; obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hb
  constructor <;> omega

theorem add_bnd {k : Nat} {a b : DN} (ha : BndD k a) (hb : BndD k b) (hk : k ≤ 254) :
    BndD (k + 1) (DN.add a b) := by
  have h1 := pow_le_254 hk; have h2 := B_eq_4
  have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha; obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hb
  simp only [BndD, InR, DN.add, Nat.add_eq, Nat.sub_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem sub_ok {k : Nat} {a b : DN} (ha : BndD k a) (hb : BndD k b) (hk : k ≤ 254) :
    b.hi ≤ a.lo + B ∧ b.lo ≤ a.hi + B := by
  have h1 := pow_le_254 hk; have h2 := B_eq_4
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha; obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hb
  constructor <;> omega

theorem sub_bnd {k : Nat} {a b : DN} (ha : BndD k a) (hb : BndD k b) (hk : k ≤ 254) :
    BndD (k + 1) (DN.sub a b) := by
  have h1 := pow_le_254 hk; have h2 := B_eq_4
  have h3 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha; obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hb
  simp only [BndD, InR, DN.sub, Nat.add_eq, Nat.sub_eq]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-! ## mul: no truncation in prodZ, and the output bound -/

theorem int_abs_of_InR {k x : Nat} (h : InR k x) : |(x : Int) - B| < 2 ^ k := by
  rw [abs_lt]; obtain ⟨h1, h2⟩ := h
  have : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by push_cast; rfl
  constructor <;> omega

theorem prod_bound {x y : Int} {k : Nat} (hx : |x| < 2 ^ k) (hy : |y| < 2 ^ k) : |x * y| < 2 ^ (2 * k) := by
  rw [abs_mul, show 2 * k = k + k by ring, pow_add]
  exact mul_lt_mul'' hx hy (abs_nonneg _) (abs_nonneg _)

/-- no truncation in `prodZ X Y` when both factors are within `2^k`, `2k <= 355` -/
theorem prodZ_ok {k X Y : Nat} (hX : InR k X) (hY : InR k Y) (hk : 2 * k ≤ 355) : (X + Y) * B ≤ X * Y + C1 := by
  have hp := prod_bound (int_abs_of_InR hX) (int_abs_of_InR hY)
  have h356 : (2 : Int) ^ (2 * k) ≤ 2 ^ 355 := pow_le_pow_right₀ (by norm_num) hk
  have hB : (B : Int) = 2 ^ 256 := by rw [B_val]; push_cast
  have key : ((X * Y + C1 : Nat) : Int) - (((X + Y) * B : Nat) : Int) =
      ((X : Int) - B) * ((Y : Int) - B) + (B : Int) * 2 ^ 100 := by
    rw [C1_val]; push_cast; ring
  have hlo := (abs_lt.1 hp).1
  have hBB : (B : Int) * 2 ^ 100 = 2 * 2 ^ 355 := by
    rw [hB, ← pow_add, show 256 + 100 = 355 + 1 from rfl, pow_succ, mul_comm]
  have hpos : (0 : Int) < 2 ^ 355 := pow_pos (by norm_num) 355
  generalize (2 : Int) ^ 355 = R at hBB hpos h356
  generalize (2 : Int) ^ (2 * k) = Q at hlo h356
  generalize ((X : Int) - B) * ((Y : Int) - B) = P at hlo key
  generalize (B : Int) * 2 ^ 100 = S at hBB key
  have h0 : (0 : Int) ≤ ((X * Y + C1 : Nat) : Int) - (((X + Y) * B : Nat) : Int) := by
    rw [key]; linarith
  exact Nat.cast_le.mp (Int.sub_nonneg.mp h0)

end S43K

#print axioms S43K.prodZ_ok
#print axioms S43K.add_bnd

end
