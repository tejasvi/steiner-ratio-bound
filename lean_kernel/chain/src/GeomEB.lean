module

public import OpLayer
public import S43.Sound.Enc

@[expose] public section

/-! # K1 function layer, part 1: enclosure + bound in one predicate

`EB k a x`: the biased-Nat interval `a` encloses the real `x` (lean/'s `Enc` of `toDI a`) and both its
endpoints lie within `2^k` of the bias (static bounds). Every op lemma consumes `EB` facts and produces one, so the bound
chain and the enclosure chain are proved together; the exponents are concrete at the function level (M = 126). Op
lemmas from `OpLayer` and DNSim/DNBound. -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- `a` encloses `x` and is within `2^k` of the bias -/
def EB (k : Nat) (a : DN) (x : ℝ) : Prop := BndD k a ∧ (toDI a).Enc x

theorem EB.mono {k k' : Nat} {a : DN} {x : ℝ} (h : EB k a x) (hk : k ≤ k') : EB k' a x := ⟨h.1.mono hk, h.2⟩

theorem EB.congr {k : Nat} {a : DN} {x y : ℝ} (h : EB k a x) (e : x = y) : EB k a y := e ▸ h

/-! ## Ops -/

theorem eb_add {k : Nat} {a b : DN} {x y : ℝ} (ha : EB k a x) (hb : EB k b y) (hk : k ≤ 254) :
    EB (k + 1) (DN.add a b) (x + y) := by
  obtain ⟨h1, h2⟩ := add_ok ha.1 hb.1 hk
  exact ⟨add_bnd ha.1 hb.1 hk, by rw [add_sim h1 h2]; exact S43.DI.enc_add ha.2 hb.2⟩

theorem eb_sub {k : Nat} {a b : DN} {x y : ℝ} (ha : EB k a x) (hb : EB k b y) (hk : k ≤ 254) :
    EB (k + 1) (DN.sub a b) (x - y) := by
  obtain ⟨h1, h2⟩ := sub_ok ha.1 hb.1 hk
  exact ⟨sub_bnd ha.1 hb.1 hk, by rw [sub_sim h1 h2]; exact S43.DI.enc_sub ha.2 hb.2⟩

theorem eb_mul {j k : Nat} {a b : DN} {x y : ℝ} (ha : EB j a x) (hb : EB k b y) (h1 : 100 ≤ j + k)
    (h2 : j + k ≤ 355) : EB (j + k - 99) (DN.mul a b) (x * y) := by
  obtain ⟨o1, o2, o3, o4⟩ := mul_ok ha.1 hb.1 h2
  exact ⟨mul_bnd ha.1 hb.1 h1 h2, by rw [mul_sim o1 o2 o3 o4]; exact S43.DI.enc_mul ha.2 hb.2⟩

theorem eb_sq {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (h1 : 100 ≤ 2 * k) (h2 : 2 * k ≤ 355) :
    EB (2 * k - 99) (DN.sq a) (x ^ 2) := by
  obtain ⟨o1, o2⟩ := sq_ok ha.1 h2
  exact ⟨sq_bnd ha.1 h1 h2, by rw [sq_sim o1 o2]; exact S43.enc_sq ha.2⟩

theorem eb_sqrt {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : k ≤ 255) : EB 179 (DN.sqrt a) (Real.sqrt x) := by
  have hb : a.hi < B + 2 ^ 256 := by
    have := ha.1.2.2
    have : 2 ^ k ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact ⟨sqrt_bnd ha.1 hk, enc_sqrtK hb ha.2⟩

theorem eb_half {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : 1 ≤ k) : EB k (DN.half a) (x / 2) :=
  ⟨half_bnd ha.1 hk, by rw [half_sim]; exact S43.DI.enc_half ha.2⟩

theorem eb_max {k : Nat} {a b : DN} {x y : ℝ} (ha : EB k a x) (hb : EB k b y) : EB k (DN.max a b) (max x y) :=
  ⟨max_bnd ha.1 hb.1, by rw [max_sim]; exact S43.enc_max ha.2 hb.2⟩

theorem eb_neg {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : k ≤ 255) : EB k (DN.neg a) (-x) := by
  obtain ⟨h1, h2⟩ := neg_ok ha.1 hk
  exact ⟨neg_bnd ha.1 hk, by rw [neg_sim h1 h2]; exact S43.DI.enc_neg ha.2⟩

theorem eb_nmul2 {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : k ≤ 254) : EB (k + 1) (DN.nmul2 a) (2 * x) := by
  obtain ⟨h1, h2⟩ := nmul2_ok ha.1 hk
  refine ⟨nmul2_bnd ha.1 hk, ?_⟩
  rw [nmul2_sim h1 h2]
  have := S43.DI.enc_nmul 2 ha.2
  simpa using this

theorem eb_nmul3 {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : k ≤ 253) : EB (k + 2) (DN.nmul3 a) (3 * x) := by
  obtain ⟨h1, h2⟩ := nmul3_ok ha.1 hk
  refine ⟨nmul3_bnd ha.1 hk, ?_⟩
  rw [nmul3_sim h1 h2]
  have := S43.DI.enc_nmul 3 ha.2
  simpa using this

theorem eb_nmul4 {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : k ≤ 253) : EB (k + 2) (DN.nmul4 a) (4 * x) := by
  obtain ⟨h1, h2⟩ := nmul4_ok ha.1 hk
  refine ⟨nmul4_bnd ha.1 hk, ?_⟩
  rw [nmul4_sim h1 h2]
  have := S43.DI.enc_nmul 4 ha.2
  simpa using this

theorem eb_divSQ3 {k : Nat} {a : DN} {x : ℝ} (ha : EB k a x) (hk : k ≤ 154) :
    EB k (DN.divD a SQ3) (x / Real.sqrt 3) :=
  ⟨divD_SQ3_bnd ha.1 hk, by rw [divD_SQ3_sim ha.1 hk]; exact S43.enc_div_SQ3 ha.2⟩

/-! ## Constants -/

theorem eb_SQ3 : EB 101 SQ3 (Real.sqrt 3) := ⟨SQ3_bnd, by rw [SQ3_sim]; exact S43.enc_SQ3⟩

theorem eb_two_over : EB 100 TWO_OVER_SQ3_M1 (2 / Real.sqrt 3 - 1) :=
  ⟨TWO_OVER_SQ3_M1_bnd, by rw [TWO_OVER_SQ3_M1_sim]; exact S43.enc_two_over⟩

theorem eb_RHO : EB 100 RHO ((2141 : ℤ) / (2500 : ℕ)) :=
  ⟨RHO_bnd, by rw [RHO_sim]; exact S43.enc_ofRat 2141 (by norm_num)⟩

theorem eb_one : EB 101 DN.one 1 := ⟨one_bnd, by rw [one_sim]; exact S43.enc_one⟩

theorem eb_ofMant {m : Nat} (hm : m < 2 ^ 126) : EB 126 (DN.ofMant m) ((m : ℤ) / 2 ^ S43.P) :=
  ⟨ofMant_bnd hm, by rw [ofMant_sim]; exact S43.enc_ofMant m⟩

/-! ## Certain comparisons (no bounds needed: the simulation is exact) -/

theorem ltcK_sound {a b : DN} {x y : ℝ} (ha : (toDI a).Enc x) (hb : (toDI b).Enc y) (h : DN.ltc a b = true) :
    x < y := S43.ltc_sound ha hb (by rw [← ltc_sim]; exact h)

theorem lecK_sound {a b : DN} {x y : ℝ} (ha : (toDI a).Enc x) (hb : (toDI b).Enc y) (h : DN.lec a b = true) :
    x ≤ y := S43.lec_sound ha hb (by rw [← lec_sim]; exact h)

theorem gecK_sound {a b : DN} {x y : ℝ} (ha : (toDI a).Enc x) (hb : (toDI b).Enc y) (h : DN.gec a b = true) :
    y ≤ x := S43.gec_sound ha hb (by rw [← gec_sim]; exact h)

theorem posK_sound {a : DN} {x : ℝ} (ha : (toDI a).Enc x) (h : DN.pos a = true) : 0 < x :=
  S43.pos_sound ha (by rw [← pos_sim]; exact h)

theorem nonposK_sound {a : DN} {x : ℝ} (ha : (toDI a).Enc x) (h : DN.nonpos a = true) : x ≤ 0 :=
  S43.nonpos_sound ha (by rw [← nonpos_sim]; exact h)

end S43K

end
