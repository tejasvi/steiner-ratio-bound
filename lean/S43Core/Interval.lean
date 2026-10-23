/-! # Dyadic intervals for the certificate checker

An interval `⟨lo, hi⟩ : DI` stands for the real interval `[lo / 2^P, hi / 2^P]` (`P = 100`). Every operation rounds outward,
so a real number in the input intervals maps into the output interval (the soundness lemmas are stated in `S43.IntervalSound`).
Comparisons are *certain*: `ltc a b` holds only if every point of `a` is below every point of `b`. Core Lean only (no Mathlib),
so that the checker compiles to native code for `native_decide`. -/

namespace S43

/-- number of fractional bits -/
def P : Nat := 100

structure DI where
  lo : Int
  hi : Int
  deriving Repr, Inhabited

namespace DI

/-- floor and ceiling of `x / 2^k` -/
@[inline] def fl (x : Int) (k : Nat := P) : Int := x >>> k
@[inline] def ce (x : Int) (k : Nat := P) : Int := -((-x) >>> k)

def ofInt (n : Int) : DI := ⟨n <<< P, n <<< P⟩
/-- the exact dyadic number `m / 2^P` -/
def ofMant (m : Int) : DI := ⟨m, m⟩
/-- enclosure of the rational `p / q` (`q > 0`) -/
def ofRat (p : Int) (q : Nat) : DI := ⟨Int.fdiv (p <<< P) q, -(Int.fdiv (-(p <<< P)) q)⟩

def zero : DI := ⟨0, 0⟩
def one : DI := ofInt 1

def add (a b : DI) : DI := ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : DI) : DI := ⟨-a.hi, -a.lo⟩
def sub (a b : DI) : DI := ⟨a.lo - b.hi, a.hi - b.lo⟩
/-- multiplication by a natural number (exact) -/
def nmul (k : Nat) (a : DI) : DI := ⟨k * a.lo, k * a.hi⟩
/-- halving, rounded outward -/
def half (a : DI) : DI := ⟨fl a.lo 1, ce a.hi 1⟩

@[inline] def imin (a b : Int) : Int := if a ≤ b then a else b
@[inline] def imax (a b : Int) : Int := if a ≤ b then b else a

def mul (a b : DI) : DI :=
  let p1 := a.lo * b.lo; let p2 := a.lo * b.hi; let p3 := a.hi * b.lo; let p4 := a.hi * b.hi
  ⟨fl (imin (imin p1 p2) (imin p3 p4)), ce (imax (imax p1 p2) (imax p3 p4))⟩

def sq (a : DI) : DI :=
  if 0 ≤ a.lo then ⟨fl (a.lo * a.lo), ce (a.hi * a.hi)⟩
  else if a.hi ≤ 0 then ⟨fl (a.hi * a.hi), ce (a.lo * a.lo)⟩
  else ⟨0, ce (imax (a.lo * a.lo) (a.hi * a.hi))⟩

/-- division by an interval that is certainly positive; `none` otherwise -/
def div (a b : DI) : Option DI :=
  if b.lo ≤ 0 then none else
  let n1 := a.lo <<< P; let n2 := a.hi <<< P
  -- the quotient set is spanned by the four endpoint quotients
  let q := [Int.fdiv n1 b.lo, Int.fdiv n1 b.hi, Int.fdiv n2 b.lo, Int.fdiv n2 b.hi]
  let r := [-(Int.fdiv (-n1) b.lo), -(Int.fdiv (-n1) b.hi), -(Int.fdiv (-n2) b.lo), -(Int.fdiv (-n2) b.hi)]
  some ⟨q.foldl imin (q.headD 0), r.foldl imax (r.headD 0)⟩

/-- enclosure of the square root of the nonnegative part -/
def sqrt (a : DI) : DI :=
  let l : Int := if a.lo ≤ 0 then 0 else (Nat.sqrt (a.lo.toNat <<< P) : Nat)
  let h : Int := if a.hi ≤ 0 then 0 else (Nat.sqrt (a.hi.toNat <<< P) : Nat) + 1
  ⟨l, h⟩

def max (a b : DI) : DI := ⟨imax a.lo b.lo, imax a.hi b.hi⟩

/-- certain comparisons -/
def ltc (a b : DI) : Bool := a.hi < b.lo
def lec (a b : DI) : Bool := a.hi ≤ b.lo
def gec (a b : DI) : Bool := b.hi ≤ a.lo
def pos (a : DI) : Bool := 0 < a.lo
def nonneg (a : DI) : Bool := 0 ≤ a.lo
def nonpos (a : DI) : Bool := a.hi ≤ 0

instance : Add DI := ⟨add⟩
instance : Sub DI := ⟨sub⟩
instance : Mul DI := ⟨mul⟩
instance : Neg DI := ⟨neg⟩

end DI

/-- `sqrt 3`, `1/2 * sqrt 3`, `2 / sqrt 3 - 1` as intervals -/
def SQ3 : DI := let s := Nat.sqrt (3 <<< (2 * P)); ⟨(s : Int), (s : Int) + 1⟩
def TWO_OVER_SQ3_M1 : DI := ((DI.ofInt 2).div SQ3).getD ⟨0, 0⟩ - DI.one

end S43
