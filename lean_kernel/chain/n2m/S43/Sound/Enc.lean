module

public import S43.IntervalSound
public import S43.Sound.Net
public import S43Core.Vertex

@[expose] public section

/-! # Enclosures: constants, the remaining interval operations, comparisons, points

`a.Enc x`: the interval `a` encloses the real `x` (`S43.IntervalSound`). Here: the constants, `sq`, `max`, `div`, `ofRat`,
`sqrt 3`, the certain comparisons, and points: `PtEnc p z` (both coordinates enclosed), `dist`, `addDir` and the
configuration points `ptsDI`/`coordsN` against `S43.Stmt.pts`. -/

namespace S43

attribute [local irreducible] P

open DI

theorem pow_P_pos : (0 : ℝ) < 2 ^ P := by positivity

theorem Enc.congr {a : DI} {x y : ℝ} (h : a.Enc x) (e : x = y) : a.Enc y := e ▸ h

theorem enc_zero : DI.zero.Enc 0 := by simp [DI.Enc, DI.zero]

theorem shiftP (n : ℤ) : ((n <<< P : ℤ) : ℝ) = 2 ^ P * n := by
  rw [Int.shiftLeft_eq]; push_cast; ring

theorem enc_ofInt (n : ℤ) : (DI.ofInt n).Enc n := by
  simp only [DI.Enc, DI.ofInt, shiftP]; exact ⟨le_refl _, le_refl _⟩

theorem enc_one : DI.one.Enc 1 := by
  have := enc_ofInt 1; simpa [DI.one] using this

theorem enc_ofMant (m : ℤ) : (DI.ofMant m).Enc ((m : ℝ) / 2 ^ P) := by
  have h := pow_P_pos
  have e : (2 : ℝ) ^ P * ((m : ℝ) / 2 ^ P) = m := by field_simp
  simp only [DI.Enc, DI.ofMant, e]; exact ⟨le_refl _, le_refl _⟩

theorem enc_ofRat (p : ℤ) {q : ℕ} (hq : 0 < q) : (DI.ofRat p q).Enc ((p : ℝ) / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqz : (0 : ℤ) ≤ (q : ℤ) := by positivity
  have hq0 : ((q : ℤ)) ≠ 0 := by exact_mod_cast hq.ne'
  have fd : ∀ a : ℤ, Int.fdiv a q = a / q := fun a => by rw [Int.fdiv_eq_ediv]; simp [hqz]
  have e : (2 : ℝ) ^ P * ((p : ℝ) / q) = (2 ^ P * p) / q := by ring
  simp only [DI.Enc, DI.ofRat, fd, e]
  constructor
  · have h1 := Int.ediv_mul_le (p <<< P) hq0
    have h1' : ((((p <<< P) / q : ℤ)) : ℝ) * q ≤ ((p <<< P : ℤ) : ℝ) := by exact_mod_cast h1
    rw [shiftP] at h1'
    rw [le_div_iff₀ hq']; exact h1'
  · have h1 := Int.ediv_mul_le (-(p <<< P)) hq0
    have h1' : ((((-(p <<< P)) / q : ℤ)) : ℝ) * q ≤ ((-(p <<< P) : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at h1' ⊢
    rw [shiftP] at h1'
    rw [div_le_iff₀ hq']; linarith

theorem enc_sq {a : DI} {x : ℝ} (ha : a.Enc x) : a.sq.Enc (x ^ 2) := by
  obtain ⟨h1, h2⟩ := ha
  have hp := pow_P_pos
  have e : (2 : ℝ) ^ P * x ^ 2 * 2 ^ P = (2 ^ P * x) ^ 2 := by ring
  unfold DI.sq
  split_ifs with hl hh
  · have hl' : (0 : ℝ) ≤ a.lo := by exact_mod_cast hl
    have f := fl_le (a.lo * a.lo) P; have c := le_ce (a.hi * a.hi) P
    push_cast at f c
    constructor
    · have : (a.lo : ℝ) * a.lo ≤ (2 ^ P * x) ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right (by rw [e]; linarith) hp
    · have : (2 ^ P * x) ^ 2 ≤ (a.hi : ℝ) * a.hi := by nlinarith
      exact le_of_mul_le_mul_right (by rw [e]; linarith) hp
  · have hh' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast hh
    have f := fl_le (a.hi * a.hi) P; have c := le_ce (a.lo * a.lo) P
    push_cast at f c
    constructor
    · have : (a.hi : ℝ) * a.hi ≤ (2 ^ P * x) ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right (by rw [e]; linarith) hp
    · have : (2 ^ P * x) ^ 2 ≤ (a.lo : ℝ) * a.lo := by nlinarith
      exact le_of_mul_le_mul_right (by rw [e]; linarith) hp
  · have c := le_ce (imax (a.lo * a.lo) (a.hi * a.hi)) P
    simp only [imax_cast, Int.cast_mul] at c
    constructor
    · simp only [Int.cast_zero]; positivity
    · have : (2 ^ P * x) ^ 2 ≤ max ((a.lo : ℝ) * a.lo) ((a.hi : ℝ) * a.hi) := by
        rcases le_total 0 (2 ^ P * x) with h | h
        · exact le_max_of_le_right (by nlinarith)
        · exact le_max_of_le_left (by nlinarith)
      exact le_of_mul_le_mul_right (by rw [e]; linarith) hp

theorem enc_max {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) : (a.max b).Enc (max x y) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  simp only [DI.Enc, DI.max, imax_cast]
  rw [mul_max_of_nonneg _ _ (le_of_lt pow_P_pos)]
  exact ⟨max_le_max h1 h3, max_le_max h2 h4⟩

/-- floor division by a positive integer, as reals -/
theorem fdiv_le {n b : ℤ} (hb : 0 < b) : ((Int.fdiv n b : ℤ) : ℝ) ≤ (n : ℝ) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [Int.fdiv_eq_ediv]; simp only [hb.le, true_or, ite_true, sub_zero]
  rw [le_div_iff₀ hb']; exact_mod_cast Int.ediv_mul_le n hb.ne'

theorem le_cdiv {n b : ℤ} (hb : 0 < b) : (n : ℝ) / b ≤ ((-(Int.fdiv (-n) b) : ℤ) : ℝ) := by
  have := fdiv_le (n := -n) hb
  push_cast at this ⊢
  rw [neg_div] at this; linarith

theorem enc_div {a b q : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) (h : a.div b = some q) : q.Enc (x / y) := by
  unfold DI.div at h
  split_ifs at h with hb0
  cases h
  have hb0' : 0 < b.lo := lt_of_not_ge hb0
  have hbh : 0 < b.hi := by
    obtain ⟨h3, h4⟩ := hb
    have : (b.lo : ℝ) ≤ b.hi := le_trans h3 h4
    have : b.lo ≤ b.hi := by exact_mod_cast this
    omega
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  have hp := pow_P_pos
  have bl : (0 : ℝ) < b.lo := by exact_mod_cast hb0'
  have bh : (0 : ℝ) < b.hi := by exact_mod_cast hbh
  have hY : 0 < 2 ^ P * y := lt_of_lt_of_le bl h3
  have hy : 0 < y := by nlinarith
  -- 2^P (x/y) = 2^P (2^P x) / (2^P y)
  have e : (2 : ℝ) ^ P * (x / y) = 2 ^ P * (2 ^ P * x) / (2 ^ P * y) := by field_simp
  have s1 : ((a.lo <<< P : ℤ) : ℝ) = 2 ^ P * a.lo := shiftP _
  have s2 : ((a.hi <<< P : ℤ) : ℝ) = 2 ^ P * a.hi := shiftP _
  simp only [DI.Enc, e, List.headD, List.foldl, imin_cast, imax_cast]
  constructor
  · -- lower end: below n1 / b.lo or n1 / b.hi, n1 = 2^P a.lo
    have key : min ((2 ^ P * a.lo : ℝ) / b.lo) ((2 ^ P * a.lo : ℝ) / b.hi) ≤ 2 ^ P * (2 ^ P * x) / (2 ^ P * y) := by
      have hx : 2 ^ P * (a.lo : ℝ) / (2 ^ P * y) ≤ 2 ^ P * (2 ^ P * x) / (2 ^ P * y) :=
        div_le_div_of_nonneg_right (by nlinarith) hY.le
      rcases le_total 0 (a.lo : ℝ) with hl | hl
      · refine le_trans (min_le_right _ _) (le_trans ?_ hx)
        exact div_le_div_of_nonneg_left (by positivity) hY h4
      · refine le_trans (min_le_left _ _) (le_trans ?_ hx)
        rw [div_le_div_iff₀ bl hY]; exact mul_le_mul_of_nonpos_left h3 (by nlinarith)
    have f1 := fdiv_le (n := a.lo <<< P) hb0'
    have f2 := fdiv_le (n := a.lo <<< P) hbh
    rw [s1] at f1 f2
    refine le_trans ?_ key
    simp only [le_min_iff]
    exact ⟨le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) f1))),
      le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) f2))⟩
  · have key : 2 ^ P * (2 ^ P * x) / (2 ^ P * y) ≤ max ((2 ^ P * a.hi : ℝ) / b.lo) ((2 ^ P * a.hi : ℝ) / b.hi) := by
      have hx : 2 ^ P * (2 ^ P * x) / (2 ^ P * y) ≤ 2 ^ P * (a.hi : ℝ) / (2 ^ P * y) :=
        div_le_div_of_nonneg_right (by nlinarith) hY.le
      rcases le_total 0 (a.hi : ℝ) with hl | hl
      · refine le_trans hx (le_trans ?_ (le_max_left _ _))
        exact div_le_div_of_nonneg_left (by positivity) bl h3
      · refine le_trans hx (le_trans ?_ (le_max_right _ _))
        rw [div_le_div_iff₀ hY bh]; exact mul_le_mul_of_nonpos_left h4 (by nlinarith)
    have f1 := le_cdiv (n := a.hi <<< P) hb0'
    have f2 := le_cdiv (n := a.hi <<< P) hbh
    rw [s2] at f1 f2
    refine le_trans key ?_
    simp only [max_le_iff]
    exact ⟨le_trans f1 (le_trans (le_max_right _ _) (le_max_left _ _)), le_trans f2 (le_max_right _ _)⟩

/-! ## sqrt 3 -/

theorem sq3_nat : (3 <<< (2 * P) : ℕ) = 3 * (2 ^ P) ^ 2 := by rw [Nat.shiftLeft_eq, ← pow_mul, mul_comm P 2]

theorem enc_SQ3 : SQ3.Enc (√3) := by
  have hp := pow_P_pos
  have h3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have lo := Nat.sqrt_le' (3 <<< (2 * P)); have hi := Nat.lt_succ_sqrt' (3 <<< (2 * P))
  set s := Nat.sqrt (3 <<< (2 * P)) with hs
  rw [sq3_nat] at lo hi
  have lo' : (s : ℝ) ^ 2 ≤ 3 * (2 ^ P) ^ 2 := by exact_mod_cast lo
  have hi' : 3 * ((2 : ℝ) ^ P) ^ 2 < ((s : ℝ) + 1) ^ 2 := by exact_mod_cast hi
  have e : (2 ^ P * √3) ^ 2 = 3 * ((2 : ℝ) ^ P) ^ 2 := by rw [mul_pow, hs3]; ring
  constructor
  · show ((s : ℤ) : ℝ) ≤ _
    push_cast
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp (by rw [e]; exact lo')
  · show _ ≤ (((s : ℤ) + 1 : ℤ) : ℝ)
    push_cast
    exact ((pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp (by rw [e]; exact hi')).le

theorem SQ3_lo_pos : 0 < SQ3.lo := by
  have h : 0 < Nat.sqrt (3 <<< (2 * P)) := Nat.sqrt_pos.mpr (by rw [sq3_nat]; positivity)
  show (0 : ℤ) < (Nat.sqrt (3 <<< (2 * P)) : ℤ)
  exact_mod_cast h

theorem div_SQ3_some (a : DI) : ∃ q, a.div SQ3 = some q := by
  unfold DI.div; rw [if_neg (by have := SQ3_lo_pos; omega)]; exact ⟨_, rfl⟩

theorem enc_div_SQ3 {a : DI} {x : ℝ} (ha : a.Enc x) : ((a.div SQ3).getD ⟨0, 0⟩).Enc (x / √3) := by
  obtain ⟨q, hq⟩ := div_SQ3_some a
  rw [hq]; exact enc_div ha enc_SQ3 hq

theorem enc_two_over : TWO_OVER_SQ3_M1.Enc (2 / √3 - 1) :=
  enc_sub (by simpa using enc_div_SQ3 (enc_ofInt 2)) enc_one

/-! ## Certain comparisons -/

theorem ltc_sound {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) (h : a.ltc b = true) : x < y := by
  have h' : a.hi < b.lo := of_decide_eq_true h
  have : (a.hi : ℝ) < b.lo := by exact_mod_cast h'
  have hp := pow_P_pos
  have := lt_of_le_of_lt ha.2 (lt_of_lt_of_le this hb.1)
  exact lt_of_mul_lt_mul_left this hp.le

theorem lec_sound {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) (h : a.lec b = true) : x ≤ y := by
  have h' : a.hi ≤ b.lo := of_decide_eq_true h
  have : (a.hi : ℝ) ≤ b.lo := by exact_mod_cast h'
  have hp := pow_P_pos
  exact le_of_mul_le_mul_left (le_trans ha.2 (le_trans this hb.1)) hp

theorem gec_sound {a b : DI} {x y : ℝ} (ha : a.Enc x) (hb : b.Enc y) (h : a.gec b = true) : y ≤ x := by
  have h' : b.hi ≤ a.lo := of_decide_eq_true h
  have : (b.hi : ℝ) ≤ a.lo := by exact_mod_cast h'
  have hp := pow_P_pos
  exact le_of_mul_le_mul_left (le_trans hb.2 (le_trans this ha.1)) hp

theorem pos_sound {a : DI} {x : ℝ} (ha : a.Enc x) (h : a.pos = true) : 0 < x := by
  have h' : 0 < a.lo := of_decide_eq_true h
  have : (0 : ℝ) < a.lo := by exact_mod_cast h'
  have hp := pow_P_pos
  have := lt_of_lt_of_le this ha.1
  exact pos_of_mul_pos_right this hp.le

theorem nonneg_sound {a : DI} {x : ℝ} (ha : a.Enc x) (h : a.nonneg = true) : 0 ≤ x := by
  have h' : 0 ≤ a.lo := of_decide_eq_true h
  have : (0 : ℝ) ≤ a.lo := by exact_mod_cast h'
  have hp := pow_P_pos
  have := le_trans this ha.1
  exact nonneg_of_mul_nonneg_right this hp

theorem nonpos_sound {a : DI} {x : ℝ} (ha : a.Enc x) (h : a.nonpos = true) : x ≤ 0 := by
  have h' : a.hi ≤ 0 := of_decide_eq_true h
  have : (a.hi : ℝ) ≤ 0 := by exact_mod_cast h'
  have hp := pow_P_pos
  have := le_trans ha.2 this
  by_contra hx; push_neg at hx
  have : 0 < (2 : ℝ) ^ P * x := mul_pos hp hx
  linarith

/-! ## Points -/

/-- a point of intervals encloses a complex number -/
def PtEnc (p : Pt) (z : ℂ) : Prop := p.1.Enc z.re ∧ p.2.Enc z.im

theorem stmt_dist_eq (z w : ℂ) : Stmt.dist z w = √((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  simp only [Stmt.dist, Complex.norm_def, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]; congr 1; ring

theorem enc_dist {a b : Pt} {za zb : ℂ} (ha : PtEnc a za) (hb : PtEnc b zb) : (S43.dist a b).Enc (Stmt.dist za zb) := by
  rw [stmt_dist_eq]
  exact enc_sqrt (enc_add (enc_sq (enc_sub ha.1 hb.1)) (enc_sq (enc_sub ha.2 hb.2)))

theorem enc_addDir {src : Pt} {z : ℂ} {t : DI} {τ : ℝ} (hs : PtEnc src z) (ht : t.Enc τ) (sgn negT : Bool) :
    PtEnc (addDir src t sgn negT) (z + ((if negT then -τ else τ : ℝ) : ℂ) * (if sgn then Stmt.dir1 else Stmt.dir2)) := by
  have h0 := enc_half ht
  have k0 : (t.half * SQ3).Enc (τ / 2 * √3) := enc_mul h0 enc_SQ3
  unfold addDir
  cases negT <;> cases sgn <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, PtEnc, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Stmt.dir1, Stmt.dir2] <;>
    refine ⟨?_, ?_⟩
  all_goals first
    | exact Enc.congr (enc_add hs.1 h0) (by ring)
    | exact Enc.congr (enc_add hs.1 (enc_neg h0)) (by ring)
    | exact Enc.congr (enc_add hs.2 k0) (by ring)
    | exact Enc.congr (enc_sub hs.2 k0) (by ring)
    | exact Enc.congr (enc_add hs.2 (enc_neg k0)) (by ring)
    | exact Enc.congr (enc_sub hs.2 (enc_neg k0)) (by ring)

/-! ## The configuration points -/

/-- the variable values enclose the case variables (by the checker's variable index) -/
def VEnc (F : Stmt.Fam) (V : Array DI) (w : Stmt.Vars) : Prop := ∀ j : ℕ, DI.Enc V[j]! (Stmt.varOf F w j)

/-- the node array encloses the configuration points -/
def PEnc (F : Stmt.Fam) (P : Array Pt) (w : Stmt.Vars) : Prop := ∀ a < Stmt.nn F, PtEnc P[a]! (Stmt.pt F w a)

theorem ptsDI_enc {I : Ids} {V : Array DI} {w : Stmt.Vars} (hb : (V[I.vb]!).Enc w.b) (hc : (V[I.vc]!).Enc w.c)
    (hd : (V[I.vd]!).Enc w.d) (hs : (V[I.vs]!).Enc w.s) (he : (V[I.ve]!).Enc w.e) (hf : (V[I.vf]!).Enc w.f)
    (hu : I.steiner = true → (V[I.vu]!).Enc w.u) (hv : I.steiner = true → (V[I.vv]!).Enc w.v) :
    let p := ptsDI I V; let q := Stmt.pts w
    PtEnc p.A q.A ∧ PtEnc p.B q.B ∧ PtEnc p.D q.D ∧ (I.steiner = true → PtEnc p.U q.U ∧ PtEnc p.V q.V) ∧
      PtEnc p.P q.P ∧ PtEnc p.Q q.Q ∧ PtEnc p.R q.R ∧ PtEnc p.s q.s ∧ PtEnc p.r q.r := by
  intro p q
  have zA : PtEnc (DI.zero, DI.zero) q.A := ⟨by simpa [q, Stmt.pts] using enc_zero, by simpa [q, Stmt.pts] using enc_zero⟩
  have zs : PtEnc (DI.one, DI.zero) q.s := ⟨by simpa [q, Stmt.pts] using enc_one, by simpa [q, Stmt.pts] using enc_zero⟩
  have zr : PtEnc (addDir (DI.one, DI.zero) V[I.vs]! false false) q.r := by
    have := enc_addDir zs hs false false
    simpa [q, Stmt.pts] using this
  have zP : PtEnc (addDir (addDir (DI.one, DI.zero) V[I.vs]! false false) V[I.vc]! true true) q.P := by
    have := enc_addDir zr hc true true
    simp only [ite_true] at this
    convert this using 1; simp [q, Stmt.pts]; ring
  have zD : PtEnc ((addDir (DI.one, DI.zero) V[I.vs]! false false).1 + V[I.vd]!,
      (addDir (DI.one, DI.zero) V[I.vs]! false false).2) q.D := by
    refine ⟨Enc.congr (enc_add zr.1 hd) ?_, Enc.congr zr.2 ?_⟩ <;> simp [q, Stmt.pts, Stmt.dir0]
  refine ⟨zA, ?_, zD, ?_, zP, ?_, ?_, zs, zr⟩
  · have := enc_addDir zs hb true false
    simpa [p, ptsDI, q, Stmt.pts] using this
  · intro hst
    simp only [p, ptsDI, hst, ite_true]
    refine ⟨?_, ?_⟩
    · have := enc_addDir zD (hu hst) true false
      simpa [q, Stmt.pts] using this
    · have := enc_addDir zD (hv hst) false false
      simpa [q, Stmt.pts] using this
  · have := enc_addDir zP hf false false
    simpa [p, ptsDI, q, Stmt.pts] using this
  · refine ⟨Enc.congr (enc_sub zP.1 he) ?_, Enc.congr zP.2 ?_⟩ <;> simp [q, Stmt.pts, Stmt.dir0]

theorem VEnc.get {F : Stmt.Fam} {V : Array DI} {w : Stmt.Vars} (h : VEnc F V w) :
    (V[(Stmt.ids F).vb]!).Enc w.b ∧ (V[(Stmt.ids F).vc]!).Enc w.c ∧ (V[(Stmt.ids F).vd]!).Enc w.d ∧ (V[(Stmt.ids F).vs]!).Enc w.s ∧
    (V[(Stmt.ids F).ve]!).Enc w.e ∧ (V[(Stmt.ids F).vf]!).Enc w.f ∧
    ((Stmt.ids F).steiner = true → (V[(Stmt.ids F).vu]!).Enc w.u ∧ (V[(Stmt.ids F).vv]!).Enc w.v) := by
  cases F
  · refine ⟨h 0, h 1, h 2, h 3, h 4, h 5, fun h' => by simp [Stmt.ids, idsReg] at h'⟩
  · exact ⟨h 0, h 1, h 2, h 3, h 6, h 7, fun _ => ⟨h 4, h 5⟩⟩

theorem coords_enc {F : Stmt.Fam} {V : Array DI} {w : Stmt.Vars} (hV : VEnc F V w) : PEnc F (coordsN (Stmt.ids F) V) w := by
  obtain ⟨hb, hc, hd, hs, he, hf, huv⟩ := hV.get
  obtain ⟨zA, zB, zD, zUV, zP, zQ, zR, zs, zr⟩ :=
    ptsDI_enc hb hc hd hs he hf (fun h => (huv h).1) (fun h => (huv h).2)
  intro a ha
  cases F
  · simp only [Stmt.nn] at ha
    interval_cases a <;> simp [coordsN, Stmt.ids, idsReg, Stmt.pt, Stmt.nodePt] <;> assumption
  · obtain ⟨zU, zV⟩ := zUV (by simp [Stmt.ids, idsSt])
    simp only [Stmt.nn] at ha
    interval_cases a <;> simp [coordsN, Stmt.ids, idsSt, Stmt.pt, Stmt.nodePt] <;> assumption

end S43

end
