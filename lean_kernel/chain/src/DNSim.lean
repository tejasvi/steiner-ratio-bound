module

public import S43CoreK.DN
public import S43Core.Interval
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Nat.Sqrt

@[expose] public section

/-! # K1: biased-Nat intervals simulate lean/'s `DI`

`toDI a` is the interval of lean/ (`DI`) that the biased-Nat interval `a` stands for. Each lemma states
`toDI (op a b) = DI.op (toDI a) (toDI b)` under the op's no-truncation conditions (the `y <= x` of each `Nat.sub`). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- the interval of lean/ (`DI`) of a biased-Nat interval -/
def toDI (a : DN) : S43.DI := ⟨(a.lo : Int) - (B : Int), (a.hi : Int) - (B : Int)⟩

theorem B_val : B = 2 ^ 256 := by decide
theorem B2_val : B2 = 2 * B := by decide
theorem B3_val : B3 = 3 * B := by decide
theorem C1_val : C1 = B * B + B * 2 ^ 100 := by decide
theorem CH_val : CH = 2 ^ 100 - 1 := by decide

theorem ble_true {x y : Nat} (h : Nat.ble x y = true) : x ≤ y := by simpa [Nat.ble_eq] using h
theorem ble_false {x y : Nat} (h : Nat.ble x y = false) : y < x := by
  have h' : ¬ (Nat.ble x y = true) := by simp [h]
  rw [Nat.ble_eq] at h'; omega

/-! ## Exact ops: add, sub, neg, nmul, half, max -/

theorem add_sim {a b : DN} (h1 : B ≤ a.lo + b.lo) (h2 : B ≤ a.hi + b.hi) :
    toDI (DN.add a b) = S43.DI.add (toDI a) (toDI b) := by
  simp only [toDI, DN.add, S43.DI.add, Nat.add_eq, Nat.sub_eq, S43.DI.mk.injEq]
  constructor <;> omega

theorem sub_sim {a b : DN} (h1 : b.hi ≤ a.lo + B) (h2 : b.lo ≤ a.hi + B) :
    toDI (DN.sub a b) = S43.DI.sub (toDI a) (toDI b) := by
  simp only [toDI, DN.sub, S43.DI.sub, Nat.add_eq, Nat.sub_eq, S43.DI.mk.injEq]
  constructor <;> omega

theorem neg_sim {a : DN} (h1 : a.hi ≤ B2) (h2 : a.lo ≤ B2) : toDI (DN.neg a) = S43.DI.neg (toDI a) := by
  have := B2_val
  simp only [toDI, DN.neg, S43.DI.neg, Nat.sub_eq, S43.DI.mk.injEq]
  constructor <;> omega

theorem nmul2_sim {a : DN} (h1 : B ≤ 2 * a.lo) (h2 : B ≤ 2 * a.hi) : toDI (DN.nmul2 a) = S43.DI.nmul 2 (toDI a) := by
  simp only [toDI, DN.nmul2, S43.DI.nmul, Nat.mul_eq, Nat.sub_eq, S43.DI.mk.injEq]
  push_cast
  constructor <;> omega

theorem nmul3_sim {a : DN} (h1 : B2 ≤ 3 * a.lo) (h2 : B2 ≤ 3 * a.hi) : toDI (DN.nmul3 a) = S43.DI.nmul 3 (toDI a) := by
  have := B2_val
  simp only [toDI, DN.nmul3, S43.DI.nmul, Nat.mul_eq, Nat.sub_eq, S43.DI.mk.injEq]
  push_cast
  constructor <;> omega

theorem half_sim (a : DN) : toDI (DN.half a) = S43.DI.half (toDI a) := by
  have hB := B_val
  simp only [toDI, DN.half, S43.DI.half, S43.DI.fl, S43.DI.ce, Nat.add_eq, S43.DI.mk.injEq, Nat.shiftRight_eq',
    Nat.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow]
  rw [hB]; push_cast
  constructor <;> omega

theorem max_sim (a b : DN) : toDI (DN.max a b) = S43.DI.max (toDI a) (toDI b) := by
  simp only [toDI, DN.max, nmax, S43.DI.max, S43.DI.imax, S43.DI.mk.injEq]
  constructor
  · cases h : Nat.ble a.lo b.lo
    · have := ble_false h; simp only [Bool.cond_false]; split_ifs <;> omega
    · have := ble_true h; simp only [Bool.cond_true]; split_ifs <;> omega
  · cases h : Nat.ble a.hi b.hi
    · have := ble_false h; simp only [Bool.cond_false]; split_ifs <;> omega
    · have := ble_true h; simp only [Bool.cond_true]; split_ifs <;> omega

/-! ## Certain comparisons -/

theorem ltc_sim (a b : DN) : DN.ltc a b = S43.DI.ltc (toDI a) (toDI b) := by
  rw [Bool.eq_iff_iff]; simp only [DN.ltc, S43.DI.ltc, Nat.blt_eq, decide_eq_true_eq]; simp only [toDI]; omega

theorem lec_sim (a b : DN) : DN.lec a b = S43.DI.lec (toDI a) (toDI b) := by
  rw [Bool.eq_iff_iff]; simp only [DN.lec, S43.DI.lec, Nat.ble_eq, decide_eq_true_eq]; simp only [toDI]; omega

theorem gec_sim (a b : DN) : DN.gec a b = S43.DI.gec (toDI a) (toDI b) := by
  rw [Bool.eq_iff_iff]; simp only [DN.gec, S43.DI.gec, Nat.ble_eq, decide_eq_true_eq]; simp only [toDI]; omega

theorem pos_sim (a : DN) : DN.pos a = S43.DI.pos (toDI a) := by
  rw [Bool.eq_iff_iff]; simp only [DN.pos, S43.DI.pos, Nat.blt_eq, decide_eq_true_eq]; simp only [toDI]; omega

theorem nonpos_sim (a : DN) : DN.nonpos a = S43.DI.nonpos (toDI a) := by
  rw [Bool.eq_iff_iff]; simp only [DN.nonpos, S43.DI.nonpos, Nat.ble_eq, decide_eq_true_eq]; simp only [toDI]; omega

/-! ## Multiplication: the biased product, its rounding, min/max -/

/-- `prodZ X Y = (X - B)(Y - B) + B 2^100` when its subtraction does not truncate -/
theorem prodZ_int {X Y : Nat} (h : (X + Y) * B ≤ X * Y + C1) :
    ((prodZ X Y : Nat) : Int) = ((X : Int) - B) * ((Y : Int) - B) + (B : Int) * 2 ^ 100 := by
  have hS : ∀ n : Nat, n <<< 256 = n * B := fun n => by rw [Nat.shiftLeft_eq, B_val]
  unfold prodZ
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.shiftLeft_eq', hS]
  rw [Nat.cast_sub h, C1_val]
  push_cast
  ring

theorem nmin_int (z1 z2 : Nat) (c : Int) :
    ((nmin z1 z2 : Nat) : Int) - c = S43.DI.imin ((z1 : Int) - c) ((z2 : Int) - c) := by
  simp only [nmin, S43.DI.imin]
  cases h : Nat.ble z1 z2
  · have := ble_false h; simp only [Bool.cond_false]; split_ifs <;> omega
  · have := ble_true h; simp only [Bool.cond_true]; split_ifs <;> omega

theorem nmax_int (z1 z2 : Nat) (c : Int) :
    ((nmax z1 z2 : Nat) : Int) - c = S43.DI.imax ((z1 : Int) - c) ((z2 : Int) - c) := by
  simp only [nmax, S43.DI.imax]
  cases h : Nat.ble z1 z2
  · have := ble_false h; simp only [Bool.cond_false]; split_ifs <;> omega
  · have := ble_true h; simp only [Bool.cond_true]; split_ifs <;> omega

theorem flZ_int (Z : Nat) : ((flZ Z : Nat) : Int) - B = S43.DI.fl ((Z : Int) - (B : Int) * 2 ^ 100) := by
  have hB := B_val
  simp only [flZ, S43.DI.fl, S43.P, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow]
  rw [hB]; push_cast; omega

theorem ceZ_int (Z : Nat) : ((ceZ Z : Nat) : Int) - B = S43.DI.ce ((Z : Int) - (B : Int) * 2 ^ 100) := by
  have hB := B_val
  simp only [ceZ, CH_val, S43.DI.ce, S43.P, Nat.add_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Int.shiftRight_eq_div_pow]
  rw [hB]; push_cast; omega

theorem mul_sim {a b : DN} (h1 : (a.lo + b.lo) * B ≤ a.lo * b.lo + C1) (h2 : (a.lo + b.hi) * B ≤ a.lo * b.hi + C1)
    (h3 : (a.hi + b.lo) * B ≤ a.hi * b.lo + C1) (h4 : (a.hi + b.hi) * B ≤ a.hi * b.hi + C1) :
    toDI (DN.mul a b) = S43.DI.mul (toDI a) (toDI b) := by
  have e1 := prodZ_int h1; have e2 := prodZ_int h2; have e3 := prodZ_int h3; have e4 := prodZ_int h4
  simp only [toDI, DN.mul, mul4, S43.DI.mul, S43.DI.mk.injEq]
  constructor
  · rw [flZ_int, nmin_int, nmin_int, nmin_int, e1, e2, e3, e4]
    simp only [add_sub_cancel_right]
  · rw [ceZ_int, nmax_int, nmax_int, nmax_int, e1, e2, e3, e4]
    simp only [add_sub_cancel_right]

/-! ## Square root (`Nat.sqrt`, as in lean/; exact when the floor checks pass) -/

theorem isFloorSqrt_eq {n s : Nat} (h : isFloorSqrt n s = true) : s = Nat.sqrt n := by
  simp only [isFloorSqrt, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.add_eq] at h
  exact Nat.eq_sqrt.2 ⟨h.1, by omega⟩

theorem toDI_eq_iff {a : DN} {d : S43.DI} : toDI a = d ↔ (a.lo : Int) - B = d.lo ∧ (a.hi : Int) - B = d.hi := by
  cases d; simp [toDI]

theorem sqrt_lo_sim {a : DN}
    (hl : B < a.lo → isFloorSqrt ((a.lo - B) <<< 100) (isqrtC ((a.lo - B) <<< 100)) = true) :
    ((DN.sqrt a).lo : Int) - B = (S43.DI.sqrt (toDI a)).lo := by
  unfold DN.sqrt sqrt2 S43.DI.sqrt toDI
  rw [show S43.P = 100 from rfl]
  dsimp only
  by_cases h : B < a.lo
  · have hs := isFloorSqrt_eq (hl h)
    have hb : Nat.ble a.lo B = false := by
      apply Bool.eq_false_iff.mpr; intro h'; have := ble_true h'; omega
    rw [hb, Bool.cond_false]
    unfold isqrtLo isqrtChk
    rw [show Nat.shiftLeft (Nat.sub a.lo B) 100 = (a.lo - B) <<< 100 from rfl, hl h, Bool.cond_true]
    have ht : ((a.lo : Int) - B).toNat = a.lo - B := by omega
    rw [ht, ← hs]
    generalize isqrtC ((a.lo - B) <<< 100) = r
    split_ifs with h0
    · omega
    · rw [show Nat.add B r = B + r from rfl]; push_cast; omega
  · have hb : Nat.ble a.lo B = true := by simp only [Nat.ble_eq]; omega
    rw [hb, Bool.cond_true]
    split_ifs with h0
    · rw [show Nat.add B 0 = B from rfl]; omega
    · omega

theorem sqrt_hi_sim {a : DN}
    (hh : B < a.hi → isFloorSqrt ((a.hi - B) <<< 100)
      (isqrtNext ((a.hi - B) <<< 100) (bif Nat.ble a.lo B then 0 else isqrtLo ((a.lo - B) <<< 100))) = true) :
    ((DN.sqrt a).hi : Int) - B = (S43.DI.sqrt (toDI a)).hi := by
  unfold DN.sqrt sqrt2 S43.DI.sqrt toDI
  rw [show S43.P = 100 from rfl]
  dsimp only
  rw [show Nat.shiftLeft (Nat.sub a.lo B) 100 = (a.lo - B) <<< 100 from rfl,
    show Nat.shiftLeft (Nat.sub a.hi B) 100 = (a.hi - B) <<< 100 from rfl]
  generalize (bif Nat.ble a.lo B then 0 else isqrtLo ((a.lo - B) <<< 100)) = sl at hh ⊢
  by_cases h : B < a.hi
  · have hs := isFloorSqrt_eq (hh h)
    have hb : Nat.ble a.hi B = false := by
      apply Bool.eq_false_iff.mpr; intro h'; have := ble_true h'; omega
    rw [hb, Bool.cond_false]
    have ht : ((a.hi : Int) - B).toNat = a.hi - B := by omega
    rw [ht, ← hs]
    generalize isqrtNext ((a.hi - B) <<< 100) sl = r
    split_ifs with h0
    · omega
    · rw [show Nat.add (Nat.add B r) 1 = B + r + 1 from rfl]; push_cast; omega
  · have hb : Nat.ble a.hi B = true := by simp only [Nat.ble_eq]; omega
    rw [hb, Bool.cond_true]
    split_ifs with h0
    · omega
    · omega

theorem sqrt_sim {a : DN}
    (hl : B < a.lo → isFloorSqrt ((a.lo - B) <<< 100) (isqrtC ((a.lo - B) <<< 100)) = true)
    (hh : B < a.hi → isFloorSqrt ((a.hi - B) <<< 100)
      (isqrtNext ((a.hi - B) <<< 100) (bif Nat.ble a.lo B then 0 else isqrtLo ((a.lo - B) <<< 100))) = true) :
    toDI (DN.sqrt a) = S43.DI.sqrt (toDI a) := by
  exact toDI_eq_iff.2 ⟨sqrt_lo_sim hl, sqrt_hi_sim hh⟩

end S43K

end
