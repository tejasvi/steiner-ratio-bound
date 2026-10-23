import S43.Sound.Box

/-! # Moving one variable: the configuration translates the part of the tree beyond its edge

Increasing the variable of an edge by `t` moves every configuration point on the far side of that edge (seen from A) by
`t δ` with a unit vector `δ`; the other points stay. Distances change by at most `t` when exactly one end moves. -/

namespace S43.Stmt

/-- the case variables -/
inductive Vr | b | c | d | s | u | v | e | f
  deriving DecidableEq

def bump (i : Vr) (t : ℝ) (w : Vars) : Vars :=
  match i with
  | .b => { w with b := w.b + t } | .c => { w with c := w.c + t } | .d => { w with d := w.d + t }
  | .s => { w with s := w.s + t } | .u => { w with u := w.u + t } | .v => { w with v := w.v + t }
  | .e => { w with e := w.e + t } | .f => { w with f := w.f + t }

/-- the configuration points as an enumeration -/
inductive Nd | A | B | D | U | V | P | Q | R | s | r
  deriving DecidableEq

def Pts.get (p : Pts) : Nd → ℂ
  | .A => p.A | .B => p.B | .D => p.D | .U => p.U | .V => p.V | .P => p.P | .Q => p.Q | .R => p.R | .s => p.s
  | .r => p.r

/-- the points beyond the edge of variable `i` (the tree A–s, B–s, s–r, r–P, r–D, P–Q, P–R, D–U, D–V, rooted at A) -/
def moved : Vr → Nd → Bool
  | .b, n => n = .B
  | .s, n => n = .r ∨ n = .P ∨ n = .D ∨ n = .Q ∨ n = .R ∨ n = .U ∨ n = .V
  | .c, n => n = .P ∨ n = .Q ∨ n = .R
  | .d, n => n = .D ∨ n = .U ∨ n = .V
  | .u, n => n = .U
  | .v, n => n = .V
  | .e, n => n = .R
  | .f, n => n = .Q

/-- the direction in which they move -/
noncomputable def delta : Vr → ℂ
  | .b => dir1 | .s => dir2 | .c => -dir1 | .d => dir0 | .u => dir1 | .v => dir2 | .e => -dir0 | .f => dir2

theorem norm_dir1 : ‖dir1‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_mk]
  simp only [dir1]
  have h : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show (1 / 2 : ℝ) * (1 / 2) + √3 / 2 * (√3 / 2) = 1 by nlinarith [h]]; simp

theorem norm_dir2 : ‖dir2‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_mk]
  simp only [dir2]
  have h : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show (1 / 2 : ℝ) * (1 / 2) + -(√3 / 2) * -(√3 / 2) = 1 by nlinarith [h]]; simp

theorem norm_delta (i : Vr) : ‖delta i‖ = 1 := by
  cases i <;> simp [delta, norm_dir1, norm_dir2, dir0]

/-- moving a variable translates exactly the points beyond its edge -/
theorem pts_bump (i : Vr) (t : ℝ) (w : Vars) (n : Nd) :
    (pts (bump i t w)).get n = (pts w).get n + (if moved i n then (t : ℂ) * delta i else 0) := by
  cases i <;> cases n <;> simp [pts, bump, Pts.get, moved, delta, dir0] <;> push_cast <;> ring

/-- distance change when one end may move: at most `t` if exactly one moves -/
theorem dist_bump_le (p q δ : ℂ) (hδ : ‖δ‖ = 1) {t : ℝ} (ht : 0 ≤ t) (m₁ m₂ : Bool) :
    dist (p + (if m₁ then (t : ℂ) * δ else 0)) (q + (if m₂ then (t : ℂ) * δ else 0)) ≤
      dist p q + (if m₁ = m₂ then 0 else t) := by
  unfold dist
  have ht' : ‖(t : ℂ) * δ‖ = t := by rw [norm_mul, hδ, Complex.norm_real, Real.norm_of_nonneg ht, mul_one]
  cases m₁ <;> cases m₂ <;> simp
  · calc ‖p - (q + (t : ℂ) * δ)‖ = ‖(p - q) - (t : ℂ) * δ‖ := by ring_nf
      _ ≤ ‖p - q‖ + ‖(t : ℂ) * δ‖ := norm_sub_le _ _
      _ = ‖p - q‖ + t := by rw [ht']
  · calc ‖p + (t : ℂ) * δ - q‖ = ‖(p - q) + (t : ℂ) * δ‖ := by ring_nf
      _ ≤ ‖p - q‖ + ‖(t : ℂ) * δ‖ := norm_add_le _ _
      _ = ‖p - q‖ + t := by rw [ht']

/-! ## Node ids of the split data -/

def nodeNd (F : Fam) (i : ℕ) : Option Nd :=
  match F with
  | .reg => [Nd.A, .B, .D, .P, .Q, .R, .s, .r][i]?
  | .st => [Nd.A, .B, .D, .U, .V, .P, .Q, .R, .s, .r][i]?

def mvId (F : Fam) (i : Vr) (id : ℕ) : Bool := (nodeNd F id).elim false (moved i)

theorem pt_eq (F : Fam) (w : Vars) (id : ℕ) : pt F w id = (nodeNd F id).elim 0 (fun n => (pts w).get n) := by
  unfold pt nodePt nodeNd
  cases F
  · by_cases h : id < 8
    · interval_cases id <;> simp [Pts.get]
    · have h1 : ∀ {α : Type} (l : List α), l.length = 8 → l[id]? = none := fun l hl => List.getElem?_eq_none (by omega)
      dsimp only
      rw [h1 _ (by simp), h1 _ (by simp)]; simp
  · by_cases h : id < 10
    · interval_cases id <;> simp [Pts.get]
    · have h1 : ∀ {α : Type} (l : List α), l.length = 10 → l[id]? = none := fun l hl => List.getElem?_eq_none (by omega)
      dsimp only
      rw [h1 _ (by simp), h1 _ (by simp)]; simp

theorem pt_bump (F : Fam) (i : Vr) (t : ℝ) (w : Vars) (id : ℕ) :
    pt F (bump i t w) id = pt F w id + (if mvId F i id then (t : ℂ) * delta i else 0) := by
  rw [pt_eq, pt_eq]
  unfold mvId
  cases h : nodeNd F id with
  | none => simp
  | some n => simp only [Option.elim]; rw [pts_bump]; by_cases hm : moved i n <;> simp [hm]

theorem dist_pt_bump (F : Fam) (i : Vr) {t : ℝ} (ht : 0 ≤ t) (w : Vars) (a b : ℕ) :
    dist (pt F (bump i t w) a) (pt F (bump i t w) b) ≤
      dist (pt F w a) (pt F w b) + (if mvId F i a = mvId F i b then 0 else t) := by
  rw [pt_bump, pt_bump]; exact dist_bump_le _ _ _ (norm_delta i) ht _ _

/-- a fold of `max` over pairs `(u, v)` with `u ≤ v + d` -/
theorem foldmax_le {d : ℝ} : ∀ (l : List (ℝ × ℝ)) (m₀ m₁ : ℝ), (∀ x ∈ l, x.1 ≤ x.2 + d) → m₀ ≤ m₁ + d →
    (l.map Prod.fst).foldl max m₀ ≤ (l.map Prod.snd).foldl max m₁ + d := by
  intro l
  induction l with
  | nil => intro m₀ m₁ _ h; simpa using h
  | cons x l ih =>
    intro m₀ m₁ hl h
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    have hx := hl x (List.mem_cons_self)
    exact max_le (by linarith [le_max_left m₁ x.2]) (by linarith [le_max_right m₁ x.2])

/-- the maximum distance from a moving centre to moving points grows by at most `d` if every distance does -/
theorem maxdist_bump_le (p p' : ℂ) (l l' : List ℂ) (hl : l.length = l'.length) {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ k (hk : k < l.length), dist p' (l'[k]'(hl ▸ hk)) ≤ dist p (l[k]'hk) + d) :
    maxdist p' l' ≤ maxdist p l + d := by
  unfold maxdist
  have e₁ : l'.map (dist p') = ((List.zipWith (fun x y => (dist p' y, dist p x)) l l').map Prod.fst) := by
    rw [List.map_zipWith]; simp only
    apply List.ext_getElem (by simp [hl]) ; intro n h1 h2; simp
  have e₂ : l.map (dist p) = ((List.zipWith (fun x y => (dist p' y, dist p x)) l l').map Prod.snd) := by
    rw [List.map_zipWith]; simp only
    apply List.ext_getElem (by simp [hl]) ; intro n h1 h2; simp
  rw [e₁, e₂]
  apply foldmax_le _ 0 0 _ (by linarith)
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  simp only [List.getElem_zipWith]
  have hk' : k < l.length := by simp at hk; omega
  exact h k hk'

/-! ## Term increments -/

theorem bump_get_ne (i : Vr) (t : ℝ) (w : Vars) (n : Nd) (h : moved i n = false) :
    (pts (bump i t w)).get n = (pts w).get n := by rw [pts_bump]; simp [h]

/-- coefficient of a lemma bound under moving variable `i` (used with lemma 0, or for `i = f`) -/
def bcoef (F : Fam) (L : ℕ) (i : Vr) : Key → ℕ
  | .Y => match F with
    | .reg => if i = .c ∨ i = .d ∨ i = .f then 1 else 0
    | .st => if i = .c ∨ i = .d ∨ i = .v ∨ i = .f then 1 else 0
  | .AX => if L = 0 then (if i = .s ∨ i = .c then 1 else 0) else 0
  | _ => 0

theorem dist_get_bump (i : Vr) {t : ℝ} (ht : 0 ≤ t) (w : Vars) (m n : Nd) :
    dist ((pts (bump i t w)).get m) ((pts (bump i t w)).get n) ≤
      dist ((pts w).get m) ((pts w).get n) + (if moved i m = moved i n then 0 else t) := by
  rw [pts_bump, pts_bump]; exact dist_bump_le _ _ _ (norm_delta i) ht _ _

theorem maxdist2_le {p p' x x' y y' : ℂ} {d : ℝ} (hd : 0 ≤ d) (hx : dist p' x' ≤ dist p x + d)
    (hy : dist p' y' ≤ dist p y + d) : maxdist p' [x', y'] ≤ maxdist p [x, y] + d := by
  simp only [maxdist, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  have := le_max_left (max 0 (dist p x)) (dist p y); have := le_max_right (max 0 (dist p x)) (dist p y)
  have := le_max_left 0 (dist p x); have := le_max_right 0 (dist p x)
  apply max_le (max_le (by linarith) (by linarith)) (by linarith)

theorem maxdist3_le {p p' x x' y y' z z' : ℂ} {d : ℝ} (hd : 0 ≤ d) (hx : dist p' x' ≤ dist p x + d)
    (hy : dist p' y' ≤ dist p y + d) (hz : dist p' z' ≤ dist p z + d) :
    maxdist p' [x', y', z'] ≤ maxdist p [x, y, z] + d := by
  simp only [maxdist, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  have := le_max_left (max (max 0 (dist p x)) (dist p y)) (dist p z)
  have := le_max_right (max (max 0 (dist p x)) (dist p y)) (dist p z)
  have := le_max_left (max 0 (dist p x)) (dist p y); have := le_max_right (max 0 (dist p x)) (dist p y)
  have := le_max_left 0 (dist p x); have := le_max_right 0 (dist p x)
  apply max_le (max_le (max_le (by linarith) (by linarith)) (by linarith)) (by linarith)

theorem bound_bump (F : Fam) (L : ℕ) (K : Key) (i : Vr) (hLi : L = 0 ∨ i = .f) {t : ℝ} (ht : 0 ≤ t) (w : Vars) :
    (lemmaBound F L K (bump i t w)).elim 0 (·.2) ≤ (lemmaBound F L K w).elim 0 (·.2) + t * bcoef F L i K := by
  have dg := fun (m n : Nd) => dist_get_bump i ht w m n
  -- the f-move leaves every point but Q, and every variable but f, unchanged
  have fA : (pts (bump .f t w)).A = (pts w).A := bump_get_ne .f t w .A rfl
  have fs : (pts (bump .f t w)).s = (pts w).s := bump_get_ne .f t w .s rfl
  have fr : (pts (bump .f t w)).r = (pts w).r := bump_get_ne .f t w .r rfl
  have fP : (pts (bump .f t w)).P = (pts w).P := bump_get_ne .f t w .P rfl
  have fR : (pts (bump .f t w)).R = (pts w).R := bump_get_ne .f t w .R rfl
  have fD : (pts (bump .f t w)).D = (pts w).D := bump_get_ne .f t w .D rfl
  have fU : (pts (bump .f t w)).U = (pts w).U := bump_get_ne .f t w .U rfl
  have fV : (pts (bump .f t w)).V = (pts w).V := bump_get_ne .f t w .V rfl
  have vb : (bump .f t w).b = w.b := rfl
  have vc : (bump .f t w).c = w.c := rfl
  have vd : (bump .f t w).d = w.d := rfl
  have vs : (bump .f t w).s = w.s := rfl
  have ve : (bump .f t w).e = w.e := rfl
  cases K
  · -- AX
    rcases hLi with rfl | rfl
    · simp only [lemmaBound, Option.elim, bcoef, if_true]
      have h1 := dg .A .r; have h2 := dg .A .P
      simp only [Pts.get] at h1 h2
      apply maxdist2_le (by positivity)
      · cases i <;> simp [moved] at h1 ⊢ <;> linarith
      · cases i <;> simp [moved] at h2 ⊢ <;> linarith
    · simp only [bcoef]
      rcases L with _ | _ | _ | _ | _ | _ | _ | _ | _ | L
      · simp only [lemmaBound, Option.elim, fA, fr, fP, if_true]
        have h1 := dg .A .r; have h2 := dg .A .P
        simp only [Pts.get, moved] at h1 h2
        apply maxdist2_le (by positivity) <;> simp_all
      all_goals simp [lemmaBound, fA, fs, fr, fP, fR, vb, vc, vd, vs, ve]
  · -- UX
    rcases hLi with rfl | rfl
    · simp [lemmaBound, bcoef]
    · simp only [lemmaBound, reduceCtorEq, ↓reduceIte, fU, fr, fP, fR, vb, vc, vd, vs, ve, bcoef]; split_ifs <;> simp
  · -- VX
    rcases hLi with rfl | rfl
    · simp [lemmaBound, bcoef]
    · simp only [lemmaBound, reduceCtorEq, ↓reduceIte, fV, fr, fP, fR, vb, vc, vd, vs, ve, bcoef]; split_ifs <;> simp
  · -- DX
    rcases hLi with rfl | rfl
    · simp [lemmaBound, bcoef]
    · simp only [lemmaBound, reduceCtorEq, ↓reduceIte, fD, fr, fP, fR, vb, vc, vd, vs, ve, bcoef]; split_ifs <;> simp
  · -- Y: the same formula in every lemma set
    cases F
    · simp only [lemmaBound, Option.elim, bcoef]
      have h1 := dg .D .P; have h2 := dg .D .Q
      simp only [Pts.get] at h1 h2
      apply maxdist2_le (by positivity)
      · cases i <;> simp [moved] at h1 ⊢ <;> linarith
      · cases i <;> simp [moved] at h2 ⊢ <;> linarith
    · simp only [lemmaBound, Option.elim, bcoef]
      have h1 := dg .V .r; have h2 := dg .V .P; have h3 := dg .V .Q
      simp only [Pts.get] at h1 h2 h3
      apply maxdist3_le (by positivity)
      · cases i <;> simp [moved] at h1 ⊢ <;> linarith
      · cases i <;> simp [moved] at h2 ⊢ <;> linarith
      · cases i <;> simp [moved] at h3 ⊢ <;> linarith

/-! ## The S+ network, S-, and the whole value -/

/-- witness after moving `i`: the star point follows the majority of its three terminals; the 4-point network keeps its
points -/
noncomputable def wbump (F : Fam) (i : Vr) (t : ℝ) (sk : SPK) (ω : Wit) : Wit :=
  match sk with
  | .star a b c =>
    let maj := (mvId F i a && mvId F i b) || (mvId F i b && mvId F i c) || (mvId F i a && mvId F i c)
    { ω with x := ω.x + (if maj then (t : ℂ) * delta i else 0) }
  | _ => ω

def scoef (F : Fam) (i : Vr) : SPK → ℕ
  | .zero => 0
  | .seg a b => if mvId F i a = mvId F i b then 0 else 1
  | .star a b c => if mvId F i a = mvId F i b ∧ mvId F i b = mvId F i c then 0 else 1
  | .pair a b c d => (if mvId F i a then 1 else 0) + (if mvId F i b then 1 else 0) + (if mvId F i c then 1 else 0) +
      (if mvId F i d then 1 else 0)

theorem spVal_bump (F : Fam) (i : Vr) {t : ℝ} (ht : 0 ≤ t) (w : Vars) (ω : Wit) (sk : SPK) :
    spVal F (bump i t w) (wbump F i t sk ω) sk ≤ spVal F w ω sk + t * scoef F i sk := by
  have hd := norm_delta i
  cases sk with
  | zero => simp [spVal, wbump, scoef]
  | seg a b =>
    simp only [spVal, wbump, scoef]
    have := dist_pt_bump F i ht w a b
    split_ifs at this ⊢ <;> simp_all
  | star a b c =>
    simp only [spVal, wbump, starLen, pt_bump, scoef]
    have h1 := dist_bump_le (pt F w a) ω.x (delta i) hd ht (mvId F i a)
      ((mvId F i a && mvId F i b) || (mvId F i b && mvId F i c) || (mvId F i a && mvId F i c))
    have h2 := dist_bump_le (pt F w b) ω.x (delta i) hd ht (mvId F i b)
      ((mvId F i a && mvId F i b) || (mvId F i b && mvId F i c) || (mvId F i a && mvId F i c))
    have h3 := dist_bump_le (pt F w c) ω.x (delta i) hd ht (mvId F i c)
      ((mvId F i a && mvId F i b) || (mvId F i b && mvId F i c) || (mvId F i a && mvId F i c))
    generalize mvId F i a = ma at h1 h2 h3 ⊢
    generalize mvId F i b = mb at h1 h2 h3 ⊢
    generalize mvId F i c = mc at h1 h2 h3 ⊢
    cases ma <;> cases mb <;> cases mc <;> simp_all <;> linarith
  | pair a b c d =>
    simp only [spVal, wbump, pairLen, pt_bump, scoef]
    have h1 := dist_bump_le (pt F w a) ω.x (delta i) hd ht (mvId F i a) false
    have h2 := dist_bump_le (pt F w b) ω.x (delta i) hd ht (mvId F i b) false
    have h3 := dist_bump_le (pt F w c) ω.y (delta i) hd ht (mvId F i c) false
    have h4 := dist_bump_le (pt F w d) ω.y (delta i) hd ht (mvId F i d) false
    generalize mvId F i a = ma at h1 h2 h3 h4 ⊢
    generalize mvId F i b = mb at h1 h2 h3 h4 ⊢
    generalize mvId F i c = mc at h1 h2 h3 h4 ⊢
    generalize mvId F i d = md at h1 h2 h3 h4 ⊢
    cases ma <;> cases mb <;> cases mc <;> cases md <;> simp_all <;> linarith

/-- the S- edge of variable `i` (edge `k ≥ 1` has the length of the checker's variable `k - 1`) -/
def vEdge (F : Fam) (i : Vr) : Option ℕ :=
  match F, i with
  | _, .b => some 1 | _, .c => some 2 | _, .d => some 3 | _, .s => some 4
  | .st, .u => some 5 | .st, .v => some 6 | .st, .e => some 7 | .st, .f => some 8
  | .reg, .e => some 5 | .reg, .f => some 6 | .reg, _ => none

def inSm (F : Fam) (i : Vr) (sp : S43.Split) : Bool := (vEdge F i).elim false (fun k => decide (k ∈ sp.sm.toList))

theorem varOf_bump (F : Fam) (i : Vr) (t : ℝ) (w : Vars) (k : ℕ) :
    varOf F (bump i t w) k = varOf F w k + (if vEdge F i = some (k + 1) then t else 0) := by
  unfold varOf
  cases F
  · dsimp only
    by_cases hk : k < 6
    · interval_cases k <;> cases i <;> simp [bump, vEdge]
    · have h0 : ∀ (l : List ℝ), l.length = 6 → l.getD k 0 = 0 := fun l hl => List.getD_eq_default _ _ (by omega)
      rw [h0 _ (by simp), h0 _ (by simp)]
      have : ∀ e, vEdge Fam.reg i = some e → e ≤ 6 := by intro e he; cases i <;> simp [vEdge] at he <;> omega
      rw [if_neg]; · simp
      intro h; have := this _ h; omega
  · dsimp only
    by_cases hk : k < 8
    · interval_cases k <;> cases i <;> simp [bump, vEdge]
    · have h0 : ∀ (l : List ℝ), l.length = 8 → l.getD k 0 = 0 := fun l hl => List.getD_eq_default _ _ (by omega)
      rw [h0 _ (by simp), h0 _ (by simp)]
      have : ∀ e, vEdge Fam.st i = some e → e ≤ 8 := by intro e he; cases i <;> simp [vEdge] at he <;> omega
      rw [if_neg]; · simp
      intro h; have := this _ h; omega

theorem sMinus_bump (F : Fam) (sp : S43.Split) (i : Vr) {t : ℝ} (ht : 0 ≤ t) (w : Vars) :
    sMinus F sp w + t * (if inSm F i sp then 1 else 0) ≤ sMinus F sp (bump i t w) := by
  have elem : ∀ k : ℕ, (if k = 0 then (1 : ℝ) else varOf F (bump i t w) (k - 1)) =
      (if k = 0 then 1 else varOf F w (k - 1)) + t * (if k ≠ 0 ∧ vEdge F i = some k then 1 else 0) := by
    intro k
    by_cases h0 : k = 0
    · simp [h0]
    · rw [if_neg h0, if_neg h0, varOf_bump, show k - 1 + 1 = k by omega]
      by_cases hv : vEdge F i = some k <;> simp [hv, h0]
  have key : ∀ l : List ℕ, (l.map fun k => if k = 0 then (1 : ℝ) else varOf F (bump i t w) (k - 1)).sum =
      (l.map fun k => if k = 0 then (1 : ℝ) else varOf F w (k - 1)).sum +
        t * (l.map fun k => if k ≠ 0 ∧ vEdge F i = some k then (1 : ℝ) else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons k l ih => rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, elem]; ring
  have nonneg : ∀ x ∈ (sp.sm.toList.map fun k => if k ≠ 0 ∧ vEdge F i = some k then (1 : ℝ) else 0), 0 ≤ x := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨k, _, rfl⟩ := hx; split_ifs <;> norm_num
  have cnt : (if inSm F i sp then (1 : ℝ) else 0) ≤
      (sp.sm.toList.map fun k => if k ≠ 0 ∧ vEdge F i = some k then (1 : ℝ) else 0).sum := by
    unfold inSm
    cases hv : vEdge F i with
    | none => simp only [Option.elim]; simp
    | some e =>
      simp only [Option.elim]
      rw [hv] at nonneg
      by_cases he : e ∈ sp.sm.toList
      · simp only [he, decide_true, if_true]
        have he' : e ∈ sp.sm.toList := he
        have hne : e ≠ 0 := by cases F <;> cases i <;> simp [vEdge] at hv <;> omega
        have hmem : (1 : ℝ) ∈ (sp.sm.toList.map fun k => if k ≠ 0 ∧ some e = some k then (1 : ℝ) else 0) := by
          rw [List.mem_map]; exact ⟨e, he', by simp [hne]⟩
        exact List.single_le_sum nonneg _ hmem
      · simp only [he, decide_false]; simp only [Bool.false_eq_true, if_false]; exact List.sum_nonneg nonneg
  unfold sMinus
  rw [key]
  nlinarith [cnt, ht]

/-! ## The whole value, the monotonicity rule, the conditions -/

def tcoef (F : Fam) (L : ℕ) (i : Vr) : TermK → ℕ
  | .seg a b => if mvId F i a = mvId F i b then 0 else 1
  | .bnd K => bcoef F L i K

theorem kVal_bump (F : Fam) (L : ℕ) (i : Vr) (hLi : L = 0 ∨ i = .f) {t : ℝ} (ht : 0 ≤ t) (w : Vars) (k : TermK) :
    kVal F L (bump i t w) k ≤ kVal F L w k + t * tcoef F L i k := by
  cases k with
  | seg a b =>
    simp only [kVal, tcoef]
    have := dist_pt_bump F i ht w a b
    split_ifs at this ⊢ <;> simp_all
  | bnd K => exact bound_bump F L K i hLi ht w

theorem sum_kVal_bump (F : Fam) (L : ℕ) (i : Vr) (hLi : L = 0 ∨ i = .f) {t : ℝ} (ht : 0 ≤ t) (w : Vars) (ks : List TermK) :
    (ks.map (kVal F L (bump i t w))).sum ≤ (ks.map (kVal F L w)).sum + t * ((ks.map (tcoef F L i)).sum : ℕ) := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    have := kVal_bump F L i hLi ht w k
    rw [Nat.cast_add, mul_add]; linarith

/-- the monotonicity rule (mono43's, with the dependencies of the bound formulas actually used) -/
def monoRule (F : Fam) (L : ℕ) (i : Vr) (sp : S43.Split) (ks : List TermK) (sk : SPK) : Bool :=
  let n := (ks.map (tcoef F L i)).sum + scoef F i sk
  (n == 0 && !inSm F i sp) || (decide (n ≤ 1) && inSm F i sp)

theorem gNet_bump_le (F : Fam) (L : ℕ) (i : Vr) (sp : S43.Split) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (ks : List TermK) (sk : SPK) (hLi : L = 0 ∨ i = .f) (hr : monoRule F L i sp ks sk = true)
    {t : ℝ} (ht : 0 ≤ t) (w : Vars) (ω : Wit) :
    gNet F L sp ρ ks sk (bump i t w) (wbump F i t sk ω) ≤ gNet F L sp ρ ks sk w ω := by
  unfold gNet
  have h1 := sum_kVal_bump F L i hLi ht w ks
  have h2 := spVal_bump F i ht w ω sk
  have h3 := sMinus_bump F sp i ht w
  set n₁ := (ks.map (tcoef F L i)).sum
  set n₂ := scoef F i sk
  have hn₁ : (0 : ℝ) ≤ n₁ := by positivity
  have hn₂ : (0 : ℝ) ≤ n₂ := by positivity
  -- ρ n₁ + n₂ - [inSm] ≤ n₁ + n₂ - [inSm] ≤ 0
  have hrule : (n₁ : ℝ) + n₂ - (if inSm F i sp then 1 else 0) ≤ 0 := by
    unfold monoRule at hr
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hr
    rcases hr with ⟨h0, hs⟩ | ⟨h1', hs⟩
    · rw [if_neg (by simp [hs])]
      have : (n₁ : ℝ) + n₂ = 0 := by exact_mod_cast h0
      linarith
    · rw [if_pos hs]
      have : ((n₁ + n₂ : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1'
      push_cast at this; linarith
  have hρn : ρ * (n₁ : ℝ) ≤ n₁ := by nlinarith
  have := mul_le_mul_of_nonneg_left h1 hρ0
  nlinarith [mul_nonneg ht hn₁, mul_nonneg ht hn₂]

/-- Phi_X does not decrease when f grows -/
theorem phiX_bump_f (w : Vars) (he : 0 ≤ w.e) (hf : 0 ≤ w.f) {t : ℝ} (ht : 0 ≤ t) : phiX w ≤ phiX (bump .f t w) := by
  unfold phiX
  simp only [bump]
  have key : √(w.e ^ 2 + w.e * (w.f + t) + (w.f + t) ^ 2) ≤ √(w.e ^ 2 + w.e * w.f + w.f ^ 2) + t := by
    rw [Real.sqrt_le_left (by positivity)]
    have hs := Real.sq_sqrt (show 0 ≤ w.e ^ 2 + w.e * w.f + w.f ^ 2 by positivity)
    have h2 : w.e + 2 * w.f ≤ 2 * √(w.e ^ 2 + w.e * w.f + w.f ^ 2) := by
      rw [show 2 * √(w.e ^ 2 + w.e * w.f + w.f ^ 2) = √(4 * (w.e ^ 2 + w.e * w.f + w.f ^ 2)) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg w.e]
    nlinarith [Real.sqrt_nonneg (w.e ^ 2 + w.e * w.f + w.f ^ 2)]
  linarith

theorem cond5_bump_f (w : Vars) (hc : 0 ≤ w.c) (he : 0 ≤ w.e) (hf : 0 ≤ w.f) {t : ℝ} (ht : 0 ≤ t) (h : cond5 w) :
    cond5 (bump .f t w) := by
  rw [cond5_iff w hc he hf] at h
  have hf' : 0 ≤ (bump .f t w).f := by simp only [bump]; linarith
  rw [cond5_iff _ (by simpa [bump] using hc) (by simpa [bump] using he) hf']
  exact ⟨by simpa [bump] using h.1, lt_of_lt_of_le h.2 (phiX_bump_f w he hf ht)⟩

/-- the vertex-checked conditions survive moving `i`: lemma 0 (c ≤ 1 for an A-X edge needs `i ≠ c`), or `i = f` with any
lemma (lemma 5 / X2 only gets easier as f grows); no Psi condition is involved (no Y2 edge on unbounded boxes) -/
theorem kVcond_bump {F : Fam} {fval L : ℕ} (i : Vr) (hLi : L = 0 ∨ i = .f) {t : ℝ} (ht : 0 ≤ t) {w : Vars}
    (hw : 0 ≤ w.c ∧ 0 ≤ w.e ∧ 0 ≤ w.f) (ω ω' : Wit) (k : TermK)
    (hc : i = .c → k ≠ .bnd .AX) (hY : F = .reg ∧ fval = 3 → k ≠ .bnd .Y)
    (h : kVcond F fval L w ω k) : kVcond F fval L (bump i t w) ω' k := by
  cases k with
  | seg a b => trivial
  | bnd K =>
    cases K with
    | Y => intro hfv; exact absurd rfl (hY hfv)
    | AX =>
      simp only [kVcond] at h ⊢
      rcases hLi with rfl | rfl
      · simp only [lemmaBound, Option.elim] at h ⊢
        cases i <;> simp_all [bump]
      · rcases L with _ | _ | _ | _ | _ | _ | _ | _ | _ | L <;> simp only [lemmaBound, Option.elim] at h ⊢ <;>
          first | exact h | (simp only [bump]; exact h) | exact cond5_bump_f w hw.1 hw.2.1 hw.2.2 ht h | simp at h
    | UX | VX | DX =>
      simp only [kVcond] at h ⊢
      rcases hLi with rfl | rfl
      · simp [lemmaBound] at h
      · simp only [lemmaBound, reduceCtorEq, ↓reduceIte] at h ⊢
        split_ifs at h ⊢
        · exact cond5_bump_f w hw.1 hw.2.1 hw.2.2 ht h
        · simp at h

end S43.Stmt
