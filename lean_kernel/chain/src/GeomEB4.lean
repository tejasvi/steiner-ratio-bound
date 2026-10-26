module

public import GeomEB3
public import S43.Sound.VertexSound

@[expose] public section

/-! # K1 function layer, part 4: witness points and the explicit networks

Every witness point of the kernel checker is `ptW X Y`: exact (lo = hi) and clamped within 2^120 of the bias, so it is a
`PB 121` enclosure of its own real point `realPtK` (lean/'s `realPt` of the interval point). The star, the five pair
candidates and the max-distances are enclosures of lean/'s `starLen` / `pairLen` / `maxdist` at explicit
points (mirror of lean/'s `enc_smt3n`, `enc_net4n`, `enc_maxdist`). -/

set_option maxRecDepth 100000

namespace S43K
open DN

/-- the interval point of lean/ for a kernel point -/
def toPt (p : PK) : S43.Pt := (toDI p.x, toDI p.y)

/-- the real point of a kernel point (lower ends; lean/'s `realPt`) -/
noncomputable def realPtK (p : PK) : ℂ := S43.realPt (toPt p)

/-! ## ptW -/

theorem clampW_bounds (X : Nat) :
    115792089237316195423570985008687907853268655437644779123584680200852849295360 ≤ clampW X ∧
      clampW X ≤ 115792089237316195423570985008687907853271313893636348955330487814973409984512 := by
  unfold clampW nmin nmax
  cases h1 : Nat.ble X 115792089237316195423570985008687907853268655437644779123584680200852849295360
  · have := ble_false h1
    simp only [Bool.cond_false]
    cases h2 : Nat.ble X 115792089237316195423570985008687907853271313893636348955330487814973409984512
    · have := ble_false h2; simp only [Bool.cond_false]; omega
    · have := ble_true h2; simp only [Bool.cond_true]; omega
  · simp only [Bool.cond_true]
    have : Nat.ble 115792089237316195423570985008687907853268655437644779123584680200852849295360
        115792089237316195423570985008687907853271313893636348955330487814973409984512 = true := by decide
    rw [this]; simp only [Bool.cond_true]; omega

theorem clampW_InR (X : Nat) : InR 121 (clampW X) := by
  have h := clampW_bounds X
  have hB : B = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide
  have h121 : (2 : Nat) ^ 121 = 2658455991569831745807614120560689152 := by norm_num
  simp only [InR, hB, h121]
  omega

theorem exact_ptW (X Y : Nat) : S43.Exact (toPt (ptW X Y)) := by
  have h1 : (ptW X Y).x.lo = (ptW X Y).x.hi := rfl
  have h2 : (ptW X Y).y.lo = (ptW X Y).y.hi := rfl
  simp only [S43.Exact, toPt, toDI, h1, h2, and_self]

theorem pb_of_exact {p : PK} (hx : BndD 121 p.x) (hy : BndD 121 p.y) (hex : S43.Exact (toPt p)) :
    PB 121 p (realPtK p) :=
  ⟨⟨hx, (S43.enc_realPt hex).1⟩, ⟨hy, (S43.enc_realPt hex).2⟩⟩

attribute [local irreducible] clampW in
/-- (never let a defeq check compare a projection of `ptW` with `clampW _`: lazy delta unfolds `clampW` and whnf then
peels successors off the 2^256-size literal; `unfold ptW` + `dsimp only` reduces the projections syntactically) -/
theorem ptW_bnd_x (X Y : Nat) : BndD 121 (ptW X Y).x := by
  unfold ptW; dsimp only; exact ⟨clampW_InR (rnd40 X), clampW_InR (rnd40 X)⟩

attribute [local irreducible] clampW in
theorem ptW_bnd_y (X Y : Nat) : BndD 121 (ptW X Y).y := by
  unfold ptW; dsimp only; exact ⟨clampW_InR (rnd40 Y), clampW_InR (rnd40 Y)⟩

theorem pb_ptW (X Y : Nat) : PB 121 (ptW X Y) (realPtK (ptW X Y)) :=
  pb_of_exact (ptW_bnd_x X Y) (ptW_bnd_y X Y) (exact_ptW X Y)

/-- a witness point: `ptW X Y` for some `X`, `Y` -/
def IsW (p : PK) : Prop := ∃ X Y, p = ptW X Y

/-- both points of a pair are witness points -/
def IsW2 (pq : PK × PK) : Prop := IsW pq.1 ∧ IsW pq.2

theorem pb_isW {p : PK} (h : IsW p) : PB 121 p (realPtK p) := by
  obtain ⟨X, Y, rfl⟩ := h; exact pb_ptW X Y

theorem isW_ptW (X Y : Nat) : IsW (ptW X Y) := ⟨X, Y, rfl⟩

theorem isW_cond {q : Bool} {a b : PK} (ha : IsW a) (hb : IsW b) : IsW (cond q a b) := by
  cases q <;> assumption

theorem isW2_cond {q : Bool} {a b : PK × PK} (ha : IsW2 a) (hb : IsW2 b) : IsW2 (cond q a b) := by
  cases q <;> assumption

theorem isW_torT (ax ay d1x d1y den tn : Nat) : IsW (torT ax ay d1x d1y den tn) :=
  isW_cond (isW_ptW _ _) (isW_ptW _ _)

theorem isW_torP (ax ay bx by_ cx cy : Nat) : IsW (torP ax ay bx by_ cx cy) := isW_torT _ _ _ _ _ _

theorem isW_fermatV (a b c : PK) : IsW (fermatV a b c) := by
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := b
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := c
  exact isW_torP _ _ _ _ _ _

theorem isW_cornerW (p : PK) : IsW (cornerW p) := by
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := p
  exact isW_ptW _ _

theorem isW_fermatR3 (ax ay bx by_ cx cy : Nat) : IsW (fermatR3 ax ay bx by_ cx cy) :=
  isW_cond (isW_ptW _ _) (isW_cond (isW_ptW _ _) (isW_cond (isW_ptW _ _) (isW_torP _ _ _ _ _ _)))

theorem isW_fermatR (a b c : PK) : IsW (fermatR a b c) := by
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := a
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := b
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := c
  exact isW_fermatR3 _ _ _ _ _ _

theorem isW2_melK (e12 e34 : Nat × Nat) (dx dy dd k1 k2 : Nat) : IsW2 (melK e12 e34 dx dy dd k1 k2) :=
  ⟨isW_ptW _ _, isW_ptW _ _⟩

theorem isW2_melD (p1 p2 p3 p4 : PK) (e12 e34 : Nat × Nat) (dx dy dd : Nat) :
    IsW2 (melD p1 p2 p3 p4 e12 e34 dx dy dd) :=
  isW2_cond ⟨isW_ptW _ _, isW_ptW _ _⟩ (isW2_melK e12 e34 dx dy dd _ _)

theorem isW2_melzakV (p1 p2 p3 p4 : PK) : IsW2 (melzakV p1 p2 p3 p4) := by
  obtain ⟨_, _⟩ := p1
  obtain ⟨_, _⟩ := p2
  obtain ⟨_, _⟩ := p3
  obtain ⟨_, _⟩ := p4
  unfold melzakV melzakF melA melE
  exact isW2_melD _ _ _ _ _ _ _ _ _

end S43K

end
