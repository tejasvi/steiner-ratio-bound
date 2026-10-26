module

public import DNBound
public import S43.IntervalSound
public import S43Core.Geom

@[expose] public section

/-! # Op layer: the remaining simulation, bound and enclosure lemmas

Context:
* `toDI a` (DNSim.lean) is the interval of lean/ `⟨a.lo - B, a.hi - B⟩` of the biased-Nat interval `a` (`B = 2^256`).
* `BndD k a` (DNBound.lean): both endpoints within `2^k` of `B`. Static bounds: every value of the checker is
  bounded, so no `Nat.sub` truncates; the `_ok` lemmas turn bounds into the no-truncation hypotheses of the `_sim`
  lemmas, the `_bnd` lemmas bound outputs.
* `DN.sqrt` uses the fallback `SQF = 2^178`.
* Patterns: DNSim.lean (`add_sim`, `mul_sim`, `sqrt_lo_sim`), DNBound.lean (`add_bnd`, `prodZ_ok`). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-! ## Helper lemmas for the proofs below -/

theorem nmax_cases (x y : Nat) : nmax x y = x ∨ nmax x y = y := by
  unfold nmax; cases Nat.ble x y <;> simp

theorem B_eq_2 : B = 2 * 2 ^ 255 := by rw [B_val]; norm_num

theorem B_eq_8 : B = 8 * 2 ^ 253 := by rw [B_val]; norm_num

theorem SQF_val : SQF = 2 ^ 178 := by decide

theorem isqrtLo_le_sqrt (n : Nat) : isqrtLo n ≤ Nat.sqrt n := by
  unfold isqrtLo isqrtChk
  generalize isqrtC n = c
  cases h : isFloorSqrt n c
  · rw [Bool.cond_false]; exact Nat.zero_le _
  · rw [Bool.cond_true]; exact (isFloorSqrt_eq h).le

theorem sqrt_lt_178 {n : Nat} (h : n < 2 ^ 356) : Nat.sqrt n < 2 ^ 178 := by
  rw [Nat.sqrt_lt']
  calc n < 2 ^ 356 := h
    _ = (2 ^ 178) ^ 2 := by rw [← pow_mul]

theorem isqrtLo_lt {n : Nat} (h : n < 2 ^ 356) : isqrtLo n < 2 ^ 178 :=
  lt_of_le_of_lt (isqrtLo_le_sqrt n) (sqrt_lt_178 h)

theorem sqrt_le_SQF {m : Nat} (hm : m < 2 ^ 356) : Nat.sqrt m ≤ SQF := by
  rw [SQF_val]; exact (sqrt_lt_178 hm).le

theorem sqrt_le_isqrtNext (m s : Nat) (hm : m < 2 ^ 356) : Nat.sqrt m ≤ isqrtNext m s := by
  unfold isqrtNext
  cases h1 : Nat.ble (Nat.add m 1) (Nat.mul (Nat.add s 1) (Nat.add s 1))
  · rw [Bool.cond_false]
    cases h2 : Nat.ble (Nat.add m 1) (Nat.mul (Nat.add s 2) (Nat.add s 2))
    · rw [Bool.cond_false]
      unfold isqrtHiF
      generalize isqrtC m = t
      cases h3 : isFloorSqrt m t
      · rw [Bool.cond_false]; exact sqrt_le_SQF hm
      · rw [Bool.cond_true]; exact (isFloorSqrt_eq h3).ge
    · rw [Bool.cond_true]
      have h := ble_true h2
      simp only [Nat.add_eq, Nat.mul_eq] at h
      apply Nat.le_of_lt_succ
      rw [Nat.sqrt_lt]
      have e : (s + 1).succ = s + 2 := rfl
      rw [e]; omega
  · rw [Bool.cond_true]
    have h := ble_true h1
    simp only [Nat.add_eq, Nat.mul_eq] at h
    apply Nat.le_of_lt_succ
    rw [Nat.sqrt_lt]
    show m < (s + 1) * (s + 1)
    omega

theorem isqrtNext_le {m s : Nat} (hs : s < 2 ^ 178) (hm : m < 2 ^ 356) : isqrtNext m s ≤ 2 ^ 178 := by
  unfold isqrtNext
  cases h1 : Nat.ble (Nat.add m 1) (Nat.mul (Nat.add s 1) (Nat.add s 1))
  · rw [Bool.cond_false]
    cases h2 : Nat.ble (Nat.add m 1) (Nat.mul (Nat.add s 2) (Nat.add s 2))
    · rw [Bool.cond_false]
      unfold isqrtHiF
      generalize isqrtC m = t
      cases h3 : isFloorSqrt m t
      · rw [Bool.cond_false, SQF_val]
      · rw [Bool.cond_true, isFloorSqrt_eq h3]; exact (sqrt_lt_178 hm).le
    · rw [Bool.cond_true]; show s + 1 ≤ 2 ^ 178; omega
  · rw [Bool.cond_true]; exact hs.le

theorem shl100_lt {d : Nat} (h : d < 2 ^ 256) : Nat.shiftLeft d 100 < 2 ^ 356 := by
  have e : Nat.shiftLeft d 100 = d * 2 ^ 100 := Nat.shiftLeft_eq d 100
  rw [e]
  calc d * 2 ^ 100 < 2 ^ 256 * 2 ^ 100 := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos 100)
    _ = 2 ^ 356 := by rw [← pow_add]

theorem imin_eq (x y : Int) : S43.DI.imin x y = min x y := rfl

theorem imax_eq (x y : Int) : S43.DI.imax x y = max x y := rfl

theorem ndiv_eq (x y : Nat) : Nat.div x y = x / y := rfl

theorem B_lit : B = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide

theorem SQ3_lo_eq : SQ3.lo = B + 2195635245840476761639769790215 := by decide

theorem SQ3_hi_eq : SQ3.hi = B + 2195635245840476761639769790216 := by decide

theorem SQ3_ble : Nat.ble SQ3.lo B = false := by decide

theorem SQ3_lo_sub : Nat.sub SQ3.lo B = 2195635245840476761639769790215 := by decide

theorem SQ3_hi_sub : Nat.sub SQ3.hi B = 2195635245840476761639769790216 := by decide

theorem nsqrt3 : Nat.sqrt (3 <<< (2 * S43.P)) = 2195635245840476761639769790215 := by
  symm
  rw [Nat.eq_sqrt]
  constructor <;> decide

theorem SQ3_val : S43.SQ3 = ⟨2195635245840476761639769790215, 2195635245840476761639769790216⟩ := by
  unfold S43.SQ3
  rw [nsqrt3]
  rfl

/-- `qfl X y` is lean/'s floor quotient for the two SQ3 divisors when `X` is within `2^154` of `B` -/
theorem qfl_int {X y : Nat} (hy : y = 2195635245840476761639769790215 ∨ y = 2195635245840476761639769790216)
    (h1 : B < X + 2 ^ 154) (h2 : X < B + 2 ^ 154) :
    ((qfl X y : Nat) : Int) - B = Int.fdiv (((X : Int) - B) <<< S43.P) (y : Int) := by
  have hB := B_lit
  have e154 : (2 : Nat) ^ 154 = 22835963083295358096932575511191922182123945984 := by norm_num
  have e100 : (2 : Nat) ^ 100 = 1267650600228229401496703205376 := by norm_num
  have e100i : (2 : Int) ^ 100 = 1267650600228229401496703205376 := by norm_num
  have hy0 : (0 : Int) ≤ (y : Int) := by omega
  rw [Int.fdiv_eq_ediv, ite_eq_left (Or.inl hy0), sub_zero, Int.shiftLeft_eq, show S43.P = 100 from rfl, e100i]
  rw [e154] at h1 h2
  unfold qfl
  cases h : Nat.ble B X
  · have hX := ble_false h
    rw [Bool.cond_false]
    simp only [Nat.sub_eq, Nat.add_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> omega
  · have hX := ble_true h
    rw [Bool.cond_true]
    simp only [Nat.sub_eq, Nat.add_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> omega

/-- `qce X y` is lean/'s ceiling quotient for the two SQ3 divisors when `X` is within `2^154` of `B` -/
theorem qce_int {X y : Nat} (hy : y = 2195635245840476761639769790215 ∨ y = 2195635245840476761639769790216)
    (h1 : B < X + 2 ^ 154) (h2 : X < B + 2 ^ 154) :
    ((qce X y : Nat) : Int) - B = -(Int.fdiv (-(((X : Int) - B) <<< S43.P)) (y : Int)) := by
  have hB := B_lit
  have e154 : (2 : Nat) ^ 154 = 22835963083295358096932575511191922182123945984 := by norm_num
  have e100 : (2 : Nat) ^ 100 = 1267650600228229401496703205376 := by norm_num
  have e100i : (2 : Int) ^ 100 = 1267650600228229401496703205376 := by norm_num
  have hy0 : (0 : Int) ≤ (y : Int) := by omega
  rw [Int.fdiv_eq_ediv, ite_eq_left (Or.inl hy0), sub_zero, Int.shiftLeft_eq, show S43.P = 100 from rfl, e100i]
  rw [e154] at h1 h2
  unfold qce
  cases h : Nat.ble B X
  · have hX := ble_false h
    rw [Bool.cond_false]
    simp only [Nat.sub_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> omega
  · have hX := ble_true h
    rw [Bool.cond_true]
    simp only [Nat.sub_eq, Nat.add_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> omega

theorem nmin_mem {P : Nat → Prop} {x y : Nat} (hx : P x) (hy : P y) : P (nmin x y) := by
  unfold nmin
  cases Nat.ble x y
  · exact hy
  · exact hx

theorem nmax_mem {P : Nat → Prop} {x y : Nat} (hx : P x) (hy : P y) : P (nmax x y) := by
  unfold nmax
  cases Nat.ble x y
  · exact hx
  · exact hy

theorem prod_bound2 {x y : Int} {j k : Nat} (hx : |x| < 2 ^ j) (hy : |y| < 2 ^ k) : |x * y| < 2 ^ (j + k) := by
  rw [abs_mul, pow_add]
  exact mul_lt_mul'' hx hy (abs_nonneg _) (abs_nonneg _)

/-- `prodZ_ok` for factors within `2^j` and `2^k` -/
theorem prodZ_ok2 {j k X Y : Nat} (hX : InR j X) (hY : InR k Y) (hjk : j + k ≤ 355) :
    (X + Y) * B ≤ X * Y + C1 := by
  have hp := prod_bound2 (int_abs_of_InR hX) (int_abs_of_InR hY)
  have h356 : (2 : Int) ^ (j + k) ≤ 2 ^ 355 := pow_le_pow_right₀ (by norm_num) hjk
  have hB : (B : Int) = 2 ^ 256 := by rw [B_val]; push_cast
  have key : ((X * Y + C1 : Nat) : Int) - (((X + Y) * B : Nat) : Int) =
      ((X : Int) - B) * ((Y : Int) - B) + (B : Int) * 2 ^ 100 := by
    rw [C1_val]; push_cast; ring
  have hlo := (abs_lt.1 hp).1
  have hBB : (B : Int) * 2 ^ 100 = 2 * 2 ^ 355 := by
    rw [hB, ← pow_add, show 256 + 100 = 355 + 1 from rfl, pow_succ, mul_comm]
  have hpos : (0 : Int) < 2 ^ 355 := pow_pos (by norm_num) 355
  generalize (2 : Int) ^ 355 = R at hBB hpos h356
  generalize (2 : Int) ^ (j + k) = Q at hlo h356
  generalize ((X : Int) - B) * ((Y : Int) - B) = P at hlo key
  generalize (B : Int) * 2 ^ 100 = S at hBB key
  have h0 : (0 : Int) ≤ ((X * Y + C1 : Nat) : Int) - (((X + Y) * B : Nat) : Int) := by
    rw [key]; linarith
  exact Nat.cast_le.mp (Int.sub_nonneg.mp h0)

/-- the biased product lies within `2^(j+k)` of `B 2^100` -/
theorem prodZ_near {j k X Y : Nat} (hX : InR j X) (hY : InR k Y) (h : (X + Y) * B ≤ X * Y + C1) :
    B * 2 ^ 100 < prodZ X Y + 2 ^ (j + k) ∧ prodZ X Y < B * 2 ^ 100 + 2 ^ (j + k) := by
  have e := prodZ_int h
  have hp := abs_lt.1 (prod_bound2 (int_abs_of_InR hX) (int_abs_of_InR hY))
  constructor
  · zify; rw [e]; linarith [hp.1]
  · zify; rw [e]; linarith [hp.2]

/-- floor and ceiling of `Z / 2^100` for `Z` within `2^m` of `B 2^100` lie within `2^(m-99)` of `B` -/
theorem fl_ce_bnd {Z m : Nat} (hm : 100 ≤ m) (h1 : B * 2 ^ 100 < Z + 2 ^ m) (h2 : Z < B * 2 ^ 100 + 2 ^ m) :
    InR (m - 99) (flZ Z) ∧ InR (m - 99) (ceZ Z) := by
  have e1 : 2 ^ m = 2 ^ (m - 100) * 2 ^ 100 := by rw [← pow_add, Nat.sub_add_cancel hm]
  have e2 : 2 ^ (m - 99) = 2 * 2 ^ (m - 100) := by
    rw [show m - 99 = (m - 100) + 1 by omega, pow_succ]; ring
  have hT : 0 < 2 ^ (m - 100) := Nat.two_pow_pos _
  have e100 : (2 : Nat) ^ 100 = 1267650600228229401496703205376 := by norm_num
  simp only [InR, flZ, ceZ, CH_val, Nat.add_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  rw [e2]
  rw [e1] at h1 h2
  generalize 2 ^ (m - 100) = T at *
  rw [e100] at h1 h2 ⊢
  generalize B = BB at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

/-- `qfl X y` stays within `2^k` of `B` for the two SQ3 divisors -/
theorem qfl_bnd {k X y : Nat} (hy : y = 2195635245840476761639769790215 ∨ y = 2195635245840476761639769790216)
    (h1 : B < X + 2 ^ k) (h2 : X < B + 2 ^ k) (hk : k ≤ 154) : InR k (qfl X y) := by
  have hB := B_lit
  have hp : 2 ^ k ≤ 2 ^ 154 := Nat.pow_le_pow_right (by norm_num) hk
  have e154 : (2 : Nat) ^ 154 = 22835963083295358096932575511191922182123945984 := by norm_num
  have e100 : (2 : Nat) ^ 100 = 1267650600228229401496703205376 := by norm_num
  have hK : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [e154] at hp
  unfold InR qfl
  generalize 2 ^ k = K at *
  cases h : Nat.ble B X
  · have hX := ble_false h
    rw [Bool.cond_false]
    simp only [Nat.sub_eq, Nat.add_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> constructor <;> omega
  · have hX := ble_true h
    rw [Bool.cond_true]
    simp only [Nat.sub_eq, Nat.add_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> constructor <;> omega

/-- `qce X y` stays within `2^k` of `B` for the two SQ3 divisors -/
theorem qce_bnd {k X y : Nat} (hy : y = 2195635245840476761639769790215 ∨ y = 2195635245840476761639769790216)
    (h1 : B < X + 2 ^ k) (h2 : X < B + 2 ^ k) (hk : k ≤ 154) : InR k (qce X y) := by
  have hB := B_lit
  have hp : 2 ^ k ≤ 2 ^ 154 := Nat.pow_le_pow_right (by norm_num) hk
  have e154 : (2 : Nat) ^ 154 = 22835963083295358096932575511191922182123945984 := by norm_num
  have e100 : (2 : Nat) ^ 100 = 1267650600228229401496703205376 := by norm_num
  have hK : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [e154] at hp
  unfold InR qce
  generalize 2 ^ k = K at *
  cases h : Nat.ble B X
  · have hX := ble_false h
    rw [Bool.cond_false]
    simp only [Nat.sub_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> constructor <;> omega
  · have hX := ble_true h
    rw [Bool.cond_true]
    simp only [Nat.sub_eq, Nat.add_eq, ndiv_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, e100]
    rcases hy with rfl | rfl <;> constructor <;> omega

/-! ## End of helper lemmas -/

/-! ## A. sqrt: widening and enclosure (the bound of the sqrt output is in C) -/

/-- the kernel sqrt interval contains the one of lean/: lo_K <= lo_N (checked floor or 0) and hi_N <= hi_K (isqrtNext's
branches are
>= floor sqrt m; branch 3 is checked or `SQF >= floor sqrt m` for `m < 2^356`) -/
theorem sqrt_widen (a : DN) (hb : a.hi < B + 2 ^ 256) :
    (toDI (DN.sqrt a)).lo ≤ (S43.DI.sqrt (toDI a)).lo ∧ (S43.DI.sqrt (toDI a)).hi ≤ (toDI (DN.sqrt a)).hi := by
  have hm : Nat.shiftLeft (Nat.sub a.hi B) 100 < 2 ^ 356 := by
    apply shl100_lt; have hB := B_val; simp only [Nat.sub_eq]; omega
  unfold DN.sqrt sqrt2 S43.DI.sqrt toDI
  rw [show S43.P = 100 from rfl]
  dsimp only
  refine ⟨?_, ?_⟩
  · by_cases h : B < a.lo
    · have hbf : Nat.ble a.lo B = false := by
        apply Bool.eq_false_iff.mpr; intro h'; have := ble_true h'; omega
      rw [hbf, Bool.cond_false, ite_eq_right (by omega)]
      have ht : ((a.lo : Int) - B).toNat = a.lo - B := by omega
      rw [ht]
      have key := isqrtLo_le_sqrt (Nat.shiftLeft (Nat.sub a.lo B) 100)
      rw [show Nat.shiftLeft (Nat.sub a.lo B) 100 = (a.lo - B) <<< 100 from rfl] at key ⊢
      generalize isqrtLo ((a.lo - B) <<< 100) = c at key ⊢
      generalize Nat.sqrt ((a.lo - B) <<< 100) = q at key ⊢
      rw [show Nat.add B c = B + c from rfl]
      push_cast
      omega
    · have hbt : Nat.ble a.lo B = true := by simp only [Nat.ble_eq]; omega
      rw [hbt, Bool.cond_true, ite_eq_left (by omega)]
      all_goals simp
  · generalize (bif Nat.ble a.lo B then 0 else isqrtLo (Nat.shiftLeft (Nat.sub a.lo B) 100)) = sl
    by_cases h : B < a.hi
    · have hbf : Nat.ble a.hi B = false := by
        apply Bool.eq_false_iff.mpr; intro h'; have := ble_true h'; omega
      rw [hbf, Bool.cond_false, ite_eq_right (by omega)]
      have ht : ((a.hi : Int) - B).toNat = a.hi - B := by omega
      rw [ht]
      have key := sqrt_le_isqrtNext (Nat.shiftLeft (Nat.sub a.hi B) 100) sl hm
      rw [show Nat.shiftLeft (Nat.sub a.hi B) 100 = (a.hi - B) <<< 100 from rfl] at key ⊢
      generalize isqrtNext ((a.hi - B) <<< 100) sl = r at key ⊢
      rw [show Nat.add (Nat.add B r) 1 = B + r + 1 from rfl]
      push_cast
      have : ((Nat.sqrt ((a.hi - B) <<< 100) : Nat) : Int) ≤ (r : Int) := by exact_mod_cast key
      linarith
    · have hbt : Nat.ble a.hi B = true := by simp only [Nat.ble_eq]; omega
      rw [hbt, Bool.cond_true, ite_eq_left (by omega)]
      simp

theorem enc_sqrtK {a : DN} {x : ℝ} (hb : a.hi < B + 2 ^ 256) (ha : (toDI a).Enc x) :
    (toDI (DN.sqrt a)).Enc (Real.sqrt x) := by
  obtain ⟨w1, w2⟩ := sqrt_widen a hb
  obtain ⟨e1, e2⟩ := S43.DI.enc_sqrt ha
  refine ⟨?_, ?_⟩
  · exact le_trans (by exact_mod_cast w1) e1
  · exact le_trans e2 (by exact_mod_cast w2)

/-! ## B. exact simulation of the remaining ops and constants -/

theorem sq_sim {a : DN} (h1 : (a.lo + a.lo) * B ≤ a.lo * a.lo + C1) (h2 : (a.hi + a.hi) * B ≤ a.hi * a.hi + C1) :
    toDI (DN.sq a) = S43.DI.sq (toDI a) := by
  have e1 := prodZ_int h1; have e2 := prodZ_int h2
  unfold DN.sq DN.sqNeg DN.sqMid S43.DI.sq
  cases hc1 : Nat.ble B a.lo
  · have hl := ble_false hc1
    rw [Bool.cond_false]
    cases hc2 : Nat.ble a.hi B
    · have hh := ble_false hc2
      rw [Bool.cond_false]
      split_ifs with s1 s2
      · simp only [toDI] at s1; omega
      · simp only [toDI] at s2; omega
      · simp only [toDI, S43.DI.mk.injEq]
        refine ⟨by omega, ?_⟩
        rw [ceZ_int, nmax_int, e1, e2]
        simp only [add_sub_cancel_right]
    · have hh := ble_true hc2
      rw [Bool.cond_true]
      split_ifs with s1 s2
      · simp only [toDI] at s1; omega
      · simp only [toDI, S43.DI.mk.injEq]
        constructor
        · rw [flZ_int, e2]; simp only [add_sub_cancel_right]
        · rw [ceZ_int, e1]; simp only [add_sub_cancel_right]
      · simp only [toDI] at s2; omega
  · have hl := ble_true hc1
    rw [Bool.cond_true]
    split_ifs with s1 s2
    · simp only [toDI, S43.DI.mk.injEq]
      constructor
      · rw [flZ_int, e1]; simp only [add_sub_cancel_right]
      · rw [ceZ_int, e2]; simp only [add_sub_cancel_right]
    all_goals (simp only [toDI] at s1; omega)

theorem nmul4_sim {a : DN} (h1 : B3 ≤ 4 * a.lo) (h2 : B3 ≤ 4 * a.hi) : toDI (DN.nmul4 a) = S43.DI.nmul 4 (toDI a) := by
  have := B3_val
  simp only [toDI, DN.nmul4, S43.DI.nmul, Nat.mul_eq, Nat.sub_eq, S43.DI.mk.injEq]
  push_cast
  constructor <;> omega

theorem dabs_sim {a : DN} (h1 : a.hi ≤ B2) (h2 : a.lo ≤ B2) : toDI (DN.dabs a) = S43.dabs (toDI a) := by
  have hB2 := B2_val
  unfold DN.dabs S43.dabs
  cases hc1 : Nat.ble B a.lo
  · have hl := ble_false hc1
    rw [Bool.cond_false]
    cases hc2 : Nat.ble a.hi B
    · have hh := ble_false hc2
      rw [Bool.cond_false]
      split_ifs with s1 s2
      · simp only [toDI] at s1; omega
      · simp only [toDI] at s2; omega
      · simp only [toDI, S43.DI.mk.injEq]
        refine ⟨by omega, ?_⟩
        rw [nmax_int]
        simp only [imax_eq, Nat.sub_eq]
        omega
    · have hh := ble_true hc2
      rw [Bool.cond_true]
      split_ifs with s1 s2
      · simp only [toDI] at s1; omega
      · exact neg_sim h1 h2
      · simp only [toDI] at s2; omega
  · have hl := ble_true hc1
    rw [Bool.cond_true]
    split_ifs with s1 s2
    · rfl
    all_goals (simp only [toDI] at s1; omega)

theorem divD_SQ3_sim {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 154) :
    toDI (DN.divD a SQ3) = ((toDI a).div S43.SQ3).getD ⟨0, 0⟩ := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hp : 2 ^ k ≤ 2 ^ 154 := Nat.pow_le_pow_right (by norm_num) hk
  have l1 : B < a.lo + 2 ^ 154 := by omega
  have l2 : a.lo < B + 2 ^ 154 := by omega
  have l3 : B < a.hi + 2 ^ 154 := by omega
  have l4 : a.hi < B + 2 ^ 154 := by omega
  have y0 : (2195635245840476761639769790215 : Nat) = 2195635245840476761639769790215 ∨
      (2195635245840476761639769790215 : Nat) = 2195635245840476761639769790216 := Or.inl rfl
  have y1 : (2195635245840476761639769790216 : Nat) = 2195635245840476761639769790215 ∨
      (2195635245840476761639769790216 : Nat) = 2195635245840476761639769790216 := Or.inr rfl
  rw [SQ3_val]
  unfold DN.divD S43.DI.div
  rw [SQ3_ble, Bool.cond_false, SQ3_lo_sub, SQ3_hi_sub, ite_eq_right (by decide), Option.getD_some]
  simp only [toDI, div2, List.foldl_cons, List.foldl_nil, List.headD_cons, S43.DI.mk.injEq]
  rw [nmin_int, nmin_int, nmin_int, nmax_int, nmax_int, nmax_int,
    qfl_int y0 l1 l2, qfl_int y1 l1 l2, qfl_int y0 l3 l4, qfl_int y1 l3 l4,
    qce_int y0 l1 l2, qce_int y1 l1 l2, qce_int y0 l3 l4, qce_int y1 l3 l4]
  push_cast
  simp only [imin_eq, imax_eq]
  constructor <;> omega

theorem SQ3_sim : toDI SQ3 = S43.SQ3 := by
  rw [SQ3_val, toDI_eq_iff, SQ3_lo_eq, SQ3_hi_eq]
  dsimp only
  constructor <;> omega

theorem TWO_OVER_SQ3_M1_sim : toDI TWO_OVER_SQ3_M1 = S43.TWO_OVER_SQ3_M1 := by
  unfold S43.TWO_OVER_SQ3_M1
  rw [SQ3_val, toDI_eq_iff]
  constructor <;> decide

theorem RHO_sim : toDI RHO = S43.DI.ofRat 2141 2500 := by
  rw [toDI_eq_iff]
  constructor <;> decide

theorem one_sim : toDI DN.one = S43.DI.one := by
  rw [toDI_eq_iff]
  constructor <;> decide

theorem zero_sim : toDI DN.zero = S43.DI.zero := by
  rw [toDI_eq_iff]
  constructor <;> decide

theorem ofMant_sim (m : Nat) : toDI (DN.ofMant m) = S43.DI.ofMant (m : Int) := by
  rw [toDI_eq_iff]
  simp only [DN.ofMant, S43.DI.ofMant, Nat.add_eq]
  constructor <;> omega

/-! ## C. no truncation from bounds, and output bounds (every op) -/

theorem mul_ok {j k : Nat} {a b : DN} (ha : BndD j a) (hb : BndD k b) (h : j + k ≤ 355) :
    (a.lo + b.lo) * B ≤ a.lo * b.lo + C1 ∧ (a.lo + b.hi) * B ≤ a.lo * b.hi + C1 ∧
      (a.hi + b.lo) * B ≤ a.hi * b.lo + C1 ∧ (a.hi + b.hi) * B ≤ a.hi * b.hi + C1 := by
  exact ⟨prodZ_ok2 ha.1 hb.1 h, prodZ_ok2 ha.1 hb.2 h, prodZ_ok2 ha.2 hb.1 h, prodZ_ok2 ha.2 hb.2 h⟩

theorem mul_bnd {j k : Nat} {a b : DN} (ha : BndD j a) (hb : BndD k b) (h1 : 100 ≤ j + k) (h2 : j + k ≤ 355) :
    BndD (j + k - 99) (DN.mul a b) := by
  obtain ⟨o1, o2, o3, o4⟩ := mul_ok ha hb h2
  have q1 := fl_ce_bnd h1 (prodZ_near ha.1 hb.1 o1).1 (prodZ_near ha.1 hb.1 o1).2
  have q2 := fl_ce_bnd h1 (prodZ_near ha.1 hb.2 o2).1 (prodZ_near ha.1 hb.2 o2).2
  have q3 := fl_ce_bnd h1 (prodZ_near ha.2 hb.1 o3).1 (prodZ_near ha.2 hb.1 o3).2
  have q4 := fl_ce_bnd h1 (prodZ_near ha.2 hb.2 o4).1 (prodZ_near ha.2 hb.2 o4).2
  unfold DN.mul DN.mul4
  simp only [BndD]
  exact ⟨nmin_mem (P := fun z => InR (j + k - 99) (flZ z))
      (nmin_mem (P := fun z => InR (j + k - 99) (flZ z)) q1.1 q2.1)
      (nmin_mem (P := fun z => InR (j + k - 99) (flZ z)) q3.1 q4.1),
    nmax_mem (P := fun z => InR (j + k - 99) (ceZ z))
      (nmax_mem (P := fun z => InR (j + k - 99) (ceZ z)) q1.2 q2.2)
      (nmax_mem (P := fun z => InR (j + k - 99) (ceZ z)) q3.2 q4.2)⟩

theorem sq_ok {k : Nat} {a : DN} (ha : BndD k a) (hk : 2 * k ≤ 355) :
    (a.lo + a.lo) * B ≤ a.lo * a.lo + C1 ∧ (a.hi + a.hi) * B ≤ a.hi * a.hi + C1 := by
  exact ⟨prodZ_ok ha.1 ha.1 hk, prodZ_ok ha.2 ha.2 hk⟩

theorem sq_bnd {k : Nat} {a : DN} (ha : BndD k a) (h1 : 100 ≤ 2 * k) (h2 : 2 * k ≤ 355) :
    BndD (2 * k - 99) (DN.sq a) := by
  obtain ⟨o1, o2⟩ := sq_ok ha h2
  rw [two_mul] at h1 ⊢
  have q1 := fl_ce_bnd h1 (prodZ_near ha.1 ha.1 o1).1 (prodZ_near ha.1 ha.1 o1).2
  have q2 := fl_ce_bnd h1 (prodZ_near ha.2 ha.2 o2).1 (prodZ_near ha.2 ha.2 o2).2
  have hP := Nat.two_pow_pos (k + k - 99)
  have hB : InR (k + k - 99) B := ⟨by omega, by omega⟩
  unfold DN.sq DN.sqNeg DN.sqMid
  cases hc1 : Nat.ble B a.lo
  · rw [Bool.cond_false]
    cases hc2 : Nat.ble a.hi B
    · rw [Bool.cond_false]
      simp only [BndD]
      exact ⟨hB, nmax_mem (P := fun z => InR (k + k - 99) (ceZ z)) q1.2 q2.2⟩
    · rw [Bool.cond_true]
      simp only [BndD]
      exact ⟨q2.1, q1.2⟩
  · rw [Bool.cond_true]
    simp only [BndD]
    exact ⟨q1.1, q2.2⟩

/-- the sqrt output, checked or fallback: below `2^179` for every input within `2^255` -/
theorem sqrt_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 255) : BndD 179 (DN.sqrt a) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hp : 2 ^ k ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) hk
  have hB := B_val
  have h256 : (2 : Nat) ^ 255 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  have hdl : Nat.sub a.lo B < 2 ^ 256 := by simp only [Nat.sub_eq]; omega
  have hdh : Nat.sub a.hi B < 2 ^ 256 := by simp only [Nat.sub_eq]; omega
  have hn := shl100_lt hdl
  have hm := shl100_lt hdh
  unfold DN.sqrt sqrt2
  have hsl : (bif Nat.ble a.lo B then 0 else isqrtLo (Nat.shiftLeft (Nat.sub a.lo B) 100)) < 2 ^ 178 := by
    cases h : Nat.ble a.lo B
    · rw [Bool.cond_false]; exact isqrtLo_lt hn
    · rw [Bool.cond_true]; exact Nat.two_pow_pos 178
  generalize (bif Nat.ble a.lo B then 0 else isqrtLo (Nat.shiftLeft (Nat.sub a.lo B) 100)) = sl at hsl ⊢
  have hnext := isqrtNext_le hsl hm
  generalize isqrtNext (Nat.shiftLeft (Nat.sub a.hi B) 100) sl = r at hnext ⊢
  have e179 : (2 : Nat) ^ 179 = 2 * 2 ^ 178 := by rw [pow_succ]; ring
  simp only [BndD, InR, Nat.add_eq]
  rw [e179]
  generalize (2 : Nat) ^ 178 = Q at *
  cases h : Nat.ble a.hi B
  · rw [Bool.cond_false]; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
  · rw [Bool.cond_true]; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem half_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : 1 ≤ k) : BndD k (DN.half a) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hK : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  simp only [BndD, InR, DN.half, Nat.add_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, pow_one]
  generalize 2 ^ k = K at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem neg_ok {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 255) : a.hi ≤ B2 ∧ a.lo ≤ B2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hp : 2 ^ k ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) hk
  have hB := B_eq_2
  have hB2 := B2_val
  generalize 2 ^ k = K at *
  generalize 2 ^ 255 = Q at *
  constructor <;> omega

theorem neg_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 255) : BndD k (DN.neg a) := by
  have hn := neg_ok ha hk
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hB2 := B2_val
  simp only [BndD, InR, DN.neg, Nat.sub_eq]
  generalize 2 ^ k = K at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem nmul2_ok {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 254) : B ≤ 2 * a.lo ∧ B ≤ 2 * a.hi := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hp : 2 ^ k ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) hk
  have hB := B_eq_4
  generalize 2 ^ k = K at *
  generalize 2 ^ 254 = Q at *
  constructor <;> omega

theorem nmul2_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 254) : BndD (k + 1) (DN.nmul2 a) := by
  have hn := nmul2_ok ha hk
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have e : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  simp only [BndD, InR, DN.nmul2, Nat.mul_eq, Nat.sub_eq, e]
  generalize 2 ^ k = K at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem nmul3_ok {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 253) : B2 ≤ 3 * a.lo ∧ B2 ≤ 3 * a.hi := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hp : 2 ^ k ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) hk
  have hB := B_eq_8
  have hB2 := B2_val
  generalize 2 ^ k = K at *
  generalize 2 ^ 253 = Q at *
  constructor <;> omega

theorem nmul3_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 253) : BndD (k + 2) (DN.nmul3 a) := by
  have hn := nmul3_ok ha hk
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have e : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  have hB2 := B2_val
  simp only [BndD, InR, DN.nmul3, Nat.mul_eq, Nat.sub_eq, e]
  generalize 2 ^ k = K at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem nmul4_ok {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 253) : B3 ≤ 4 * a.lo ∧ B3 ≤ 4 * a.hi := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have hp : 2 ^ k ≤ 2 ^ 253 := Nat.pow_le_pow_right (by norm_num) hk
  have hB := B_eq_8
  have hB3 := B3_val
  generalize 2 ^ k = K at *
  generalize 2 ^ 253 = Q at *
  constructor <;> omega

theorem nmul4_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 253) : BndD (k + 2) (DN.nmul4 a) := by
  have hn := nmul4_ok ha hk
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have e : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  have hB3 := B3_val
  simp only [BndD, InR, DN.nmul4, Nat.mul_eq, Nat.sub_eq, e]
  generalize 2 ^ k = K at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem max_bnd {k : Nat} {a b : DN} (ha : BndD k a) (hb : BndD k b) : BndD k (DN.max a b) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha; obtain ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩ := hb
  simp only [BndD, InR, DN.max]
  rcases nmax_cases a.lo b.lo with e1 | e1 <;> rcases nmax_cases a.hi b.hi with e2 | e2 <;> rw [e1, e2] <;>
    exact ⟨⟨by assumption, by assumption⟩, ⟨by assumption, by assumption⟩⟩

theorem dabs_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 255) : BndD k (DN.dabs a) := by
  unfold DN.dabs
  cases h1 : Nat.ble B a.lo
  · rw [Bool.cond_false]
    cases h2 : Nat.ble a.hi B
    · rw [Bool.cond_false]
      have hl := ble_false h1
      obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha
      have hB2 := B2_val
      have hK : 0 < 2 ^ k := Nat.two_pow_pos k
      simp only [BndD, InR]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rcases nmax_cases (Nat.sub B2 a.lo) a.hi with e | e <;> rw [e]
      · simp only [Nat.sub_eq]; constructor <;> omega
      · exact ⟨a3, a4⟩
    · rw [Bool.cond_true]; exact neg_bnd ha hk
  · rw [Bool.cond_true]; exact ha

theorem divD_SQ3_bnd {k : Nat} {a : DN} (ha : BndD k a) (hk : k ≤ 154) : BndD k (DN.divD a SQ3) := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := ha
  have y0 : (2195635245840476761639769790215 : Nat) = 2195635245840476761639769790215 ∨
      (2195635245840476761639769790215 : Nat) = 2195635245840476761639769790216 := Or.inl rfl
  have y1 : (2195635245840476761639769790216 : Nat) = 2195635245840476761639769790215 ∨
      (2195635245840476761639769790216 : Nat) = 2195635245840476761639769790216 := Or.inr rfl
  unfold DN.divD
  rw [SQ3_ble, Bool.cond_false, SQ3_lo_sub, SQ3_hi_sub]
  unfold DN.div2
  simp only [BndD]
  exact ⟨nmin_mem (P := InR k) (nmin_mem (P := InR k) (qfl_bnd y0 h1 h2 hk) (qfl_bnd y1 h1 h2 hk))
      (nmin_mem (P := InR k) (qfl_bnd y0 h3 h4 hk) (qfl_bnd y1 h3 h4 hk)),
    nmax_mem (P := InR k) (nmax_mem (P := InR k) (qce_bnd y0 h1 h2 hk) (qce_bnd y1 h1 h2 hk))
      (nmax_mem (P := InR k) (qce_bnd y0 h3 h4 hk) (qce_bnd y1 h3 h4 hk))⟩

theorem RHO_bnd : BndD 100 RHO := by
  unfold BndD InR; decide

theorem SQ3_bnd : BndD 101 SQ3 := by
  unfold BndD InR; decide

theorem TWO_OVER_SQ3_M1_bnd : BndD 100 TWO_OVER_SQ3_M1 := by
  unfold BndD InR; decide

theorem one_bnd : BndD 101 DN.one := by
  unfold BndD InR; decide

theorem ofMant_bnd {m : Nat} (hm : m < 2 ^ 126) : BndD 126 (DN.ofMant m) := by
  simp only [BndD, InR, DN.ofMant, Nat.add_eq]
  generalize 2 ^ 126 = K at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

end S43K

end
