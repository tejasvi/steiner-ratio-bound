module

public import GeomEB
public import S43CoreK.GeomK

@[expose] public section

/-! # K1 function layer, part 2: points and distances

`PB k p z`: both coordinates of the kernel point `p` are `EB k` enclosures of `z.re`, `z.im` (lean/'s `PtEnc` plus
bounds). Mirrors lean/'s `enc_dist`, `enc_addDir`, `ptsDI_enc` (S43/Sound/Enc.lean). Exponents at M = 126: the configuration points
are within 2^135, distances within 2^179. -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- a kernel point encloses `z` within `2^k` -/
def PB (k : Nat) (p : PK) (z : ℂ) : Prop := EB k p.x z.re ∧ EB k p.y z.im

theorem PB.mono {k k' : Nat} {p : PK} {z : ℂ} (h : PB k p z) (hk : k ≤ k') : PB k' p z := ⟨h.1.mono hk, h.2.mono hk⟩

theorem eb_zero : EB 1 DN.zero 0 := by
  refine ⟨?_, by rw [zero_sim]; exact S43.enc_zero⟩
  simp only [BndD, InR, DN.zero]; constructor <;> constructor <;> omega

theorem pb_S0 : PB 101 S0 (1 : ℂ) := by
  show EB 101 DN.one (1 : ℂ).re ∧ EB 101 DN.zero (1 : ℂ).im
  rw [Complex.one_re, Complex.one_im]
  exact ⟨eb_one, eb_zero.mono (by norm_num)⟩

/-! ## Distance -/

theorem eb_dist {n : Nat} {a b : PK} {za zb : ℂ} (ha : PB n a za) (hb : PB n b zb) (hn1 : 50 ≤ n) (hn2 : n ≤ 175) :
    EB 179 (dist a b) (S43.Stmt.dist za zb) := by
  rw [S43.stmt_dist_eq]
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, by_⟩ := b
  have hx := eb_sub ha.1 hb.1 (by omega)
  have hy := eb_sub ha.2 hb.2 (by omega)
  have sx := eb_sq hx (by omega) (by omega)
  have sy := eb_sq hy (by omega) (by omega)
  have sxy := eb_add sx sy (by omega)
  exact eb_sqrt sxy (by omega)

/-! ## addDir -/

theorem pb_addDir {n : Nat} {src : PK} {z : ℂ} {t : DN} {τ : ℝ} (hs : PB n src z) (ht : EB n t τ) (hn : 1 ≤ n)
    (hn2 : n ≤ 251) (sgn negT : Bool) :
    PB (n + 3) (addDir src t sgn negT)
      (z + ((if negT then -τ else τ : ℝ) : ℂ) * (if sgn then S43.Stmt.dir1 else S43.Stmt.dir2)) := by
  have h0 : EB n (DN.half t) (τ / 2) := eb_half ht hn
  have k0 : EB (n + 2) (DN.mul (DN.half t) SQ3) (τ / 2 * Real.sqrt 3) := by
    have := eb_mul h0 eb_SQ3 (by omega) (by omega)
    rwa [show n + 101 - 99 = n + 2 by omega] at this
  have h0' := h0.mono (show n ≤ n + 2 by omega)
  have hx := hs.1.mono (show n ≤ n + 2 by omega)
  have hy := hs.2.mono (show n ≤ n + 2 by omega)
  have nh0 := (eb_neg h0 (by omega)).mono (show n ≤ n + 2 by omega)
  have nk0 := eb_neg k0 (by omega)
  obtain ⟨sx, sy⟩ := src
  have re1 : ∀ c : ℝ, (z + (c : ℂ) * S43.Stmt.dir1).re = z.re + c / 2 := by
    intro c; simp [S43.Stmt.dir1, Complex.add_re, Complex.mul_re]; ring
  have im1 : ∀ c : ℝ, (z + (c : ℂ) * S43.Stmt.dir1).im = z.im + c / 2 * Real.sqrt 3 := by
    intro c; simp [S43.Stmt.dir1, Complex.add_im, Complex.mul_im]; ring
  have re2 : ∀ c : ℝ, (z + (c : ℂ) * S43.Stmt.dir2).re = z.re + c / 2 := by
    intro c; simp [S43.Stmt.dir2, Complex.add_re, Complex.mul_re]; ring
  have im2 : ∀ c : ℝ, (z + (c : ℂ) * S43.Stmt.dir2).im = z.im - c / 2 * Real.sqrt 3 := by
    intro c; simp [S43.Stmt.dir2, Complex.add_im, Complex.mul_im]; ring
  cases negT <;> cases sgn
  · show EB (n + 3) (DN.add sx (DN.half t)) _ ∧ EB (n + 3) (DN.sub sy (DN.mul (DN.half t) SQ3)) _
    simp only [Bool.false_eq_true, ite_false, re2, im2]
    exact ⟨(eb_add hx h0' (by omega)).congr (by ring), (eb_sub hy k0 (by omega)).congr (by ring)⟩
  · show EB (n + 3) (DN.add sx (DN.half t)) _ ∧ EB (n + 3) (DN.add sy (DN.mul (DN.half t) SQ3)) _
    simp only [Bool.false_eq_true, ite_false, ite_true, re1, im1]
    exact ⟨(eb_add hx h0' (by omega)).congr (by ring), (eb_add hy k0 (by omega)).congr (by ring)⟩
  · show EB (n + 3) (DN.add sx (DN.neg (DN.half t))) _ ∧
      EB (n + 3) (DN.sub sy (DN.neg (DN.mul (DN.half t) SQ3))) _
    simp only [Bool.false_eq_true, ite_false, ite_true, re2, im2]
    exact ⟨(eb_add hx nh0 (by omega)).congr (by ring), (eb_sub hy nk0 (by omega)).congr (by ring)⟩
  · show EB (n + 3) (DN.add sx (DN.neg (DN.half t))) _ ∧
      EB (n + 3) (DN.add sy (DN.neg (DN.mul (DN.half t) SQ3))) _
    simp only [ite_true, re1, im1]
    exact ⟨(eb_add hx nh0 (by omega)).congr (by ring), (eb_add hy nk0 (by omega)).congr (by ring)⟩

end S43K

end
