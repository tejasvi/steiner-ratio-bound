module

public import S43CoreK.Ladder

@[expose] public section

/-! # Biased-Nat dyadic intervals for the kernel checker

`⟨X, Y⟩ : DN` stands for lean/'s `⟨X - B, Y - B⟩ : S43.DI` (`B = 2^256`; scale 2^-100). Every operation below returns
exactly lean/'s `S43.DI` operation shifted by `B`, provided every endpoint `x` involved satisfies `|x| < 2^170` (then no
truncated subtraction occurs). Each operation is a handful of GMP-accelerated `Nat` steps in the kernel, against
~20 kernel steps for each `Int` operation. Core Lean only; no `let`s, no type-class arithmetic in the hot paths. -/

namespace S43K

def B : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
def B2 : Nat := 231584178474632390847141970017375815706539969331281128078915168015826259279872
def B3 : Nat := 347376267711948586270712955026063723559809953996921692118372752023739388919808
/-- `B^2 + B 2^100` -/
def C1 : Nat := 13407807929942597099574024998205846127479365820739177289146926020464856567372880541012854457473673419609237543907249114923416910528427757345481692945580032
/-- `2^100 - 1` -/
def CH : Nat := 1267650600228229401496703205375

structure DN where
  lo : Nat
  hi : Nat

namespace DN
def zero : DN := ⟨B, B⟩
def one : DN := ⟨115792089237316195423570985008687907853269984666908214639685813409409832845312, 115792089237316195423570985008687907853269984666908214639685813409409832845312⟩
def two : DN := ⟨115792089237316195423570985008687907853269984668175865239914042810906536050688, 115792089237316195423570985008687907853269984668175865239914042810906536050688⟩
/-- lean/'s `DI.ofMant m` for a box mantissa `m >= 0` -/
def ofMant (m : Nat) : DN := ⟨Nat.add B m, Nat.add B m⟩

def add (a b : DN) : DN := ⟨Nat.sub (Nat.add a.lo b.lo) B, Nat.sub (Nat.add a.hi b.hi) B⟩
def sub (a b : DN) : DN := ⟨Nat.sub (Nat.add a.lo B) b.hi, Nat.sub (Nat.add a.hi B) b.lo⟩
def neg (a : DN) : DN := ⟨Nat.sub B2 a.hi, Nat.sub B2 a.lo⟩
/-- lean/'s `nmul 2/3/4`: `k x + B = k X - (k-1) B` -/
def nmul2 (a : DN) : DN := ⟨Nat.sub (Nat.mul 2 a.lo) B, Nat.sub (Nat.mul 2 a.hi) B⟩
def nmul3 (a : DN) : DN := ⟨Nat.sub (Nat.mul 3 a.lo) B2, Nat.sub (Nat.mul 3 a.hi) B2⟩
def nmul4 (a : DN) : DN := ⟨Nat.sub (Nat.mul 4 a.lo) B3, Nat.sub (Nat.mul 4 a.hi) B3⟩
/-- lean/'s `half` = `⟨floor(lo/2), ceil(hi/2)⟩` -/
def half (a : DN) : DN := ⟨Nat.shiftRight (Nat.add a.lo B) 1, Nat.shiftRight (Nat.add (Nat.add a.hi B) 1) 1⟩

/-- `x y + B 2^100` (exact product at scale 2^-200, biased) for `X = x + B`, `Y = y + B` -/
def prodZ (X Y : Nat) : Nat := Nat.sub (Nat.add (Nat.mul X Y) C1) (Nat.shiftLeft (Nat.add X Y) 256)
def flZ (Z : Nat) : Nat := Nat.shiftRight Z 100
def ceZ (Z : Nat) : Nat := Nat.shiftRight (Nat.add Z CH) 100
def nmin (a b : Nat) : Nat := bif Nat.ble a b then a else b
def nmax (a b : Nat) : Nat := bif Nat.ble a b then b else a
def mul4 (z1 z2 z3 z4 : Nat) : DN := ⟨flZ (nmin (nmin z1 z2) (nmin z3 z4)), ceZ (nmax (nmax z1 z2) (nmax z3 z4))⟩
/-- lean/'s `mul` -/
def mul (a b : DN) : DN := mul4 (prodZ a.lo b.lo) (prodZ a.lo b.hi) (prodZ a.hi b.lo) (prodZ a.hi b.hi)
def sqMid (a : DN) : DN := ⟨B, ceZ (nmax (prodZ a.lo a.lo) (prodZ a.hi a.hi))⟩
def sqNeg (a : DN) : DN := bif Nat.ble a.hi B then ⟨flZ (prodZ a.hi a.hi), ceZ (prodZ a.lo a.lo)⟩ else sqMid a
/-- lean/'s `sq` -/
def sq (a : DN) : DN := bif Nat.ble B a.lo then ⟨flZ (prodZ a.lo a.lo), ceZ (prodZ a.hi a.hi)⟩ else sqNeg a
/-- lean/'s `max` -/
def max (a b : DN) : DN := ⟨nmax a.lo b.lo, nmax a.hi b.hi⟩

/-! ## Division by a certainly positive interval (lean/'s `div`; `none` = not certainly positive) -/
/-- floor((X - B) 2^100 / y) + B for y > 0 -/
def qfl (X y : Nat) : Nat :=
  bif Nat.ble B X then Nat.add B (Nat.div (Nat.shiftLeft (Nat.sub X B) 100) y)
  else Nat.sub B (Nat.div (Nat.sub (Nat.add (Nat.shiftLeft (Nat.sub B X) 100) y) 1) y)
/-- ceil((X - B) 2^100 / y) + B for y > 0 -/
def qce (X y : Nat) : Nat :=
  bif Nat.ble B X then Nat.add B (Nat.div (Nat.sub (Nat.add (Nat.shiftLeft (Nat.sub X B) 100) y) 1) y)
  else Nat.sub B (Nat.div (Nat.shiftLeft (Nat.sub B X) 100) y)
def div2 (a : DN) (yl yh : Nat) : DN :=
  ⟨nmin (nmin (qfl a.lo yl) (qfl a.lo yh)) (nmin (qfl a.hi yl) (qfl a.hi yh)),
   nmax (nmax (qce a.lo yl) (qce a.lo yh)) (nmax (qce a.hi yl) (qce a.hi yh))⟩
def div (a b : DN) : Option DN := bif Nat.ble b.lo B then none else some (div2 a (Nat.sub b.lo B) (Nat.sub b.hi B))
/-- `(a.div b).getD ⟨0, 0⟩` -/
def divD (a b : DN) : DN := bif Nat.ble b.lo B then zero else div2 a (Nat.sub b.lo B) (Nat.sub b.hi B)

/-! ## Square root (lean/'s `sqrt`: lo = floor(sqrt(lo 2^100)), hi = floor(sqrt(hi 2^100)) + 1; 0 for nonpositive ends) -/
def nstep (n x : Nat) : Nat := Nat.shiftRight (Nat.add x (Nat.div n x)) 1
def newton8 (n x : Nat) : Nat := nstep n (nstep n (nstep n (nstep n (nstep n (nstep n (nstep n (nstep n x)))))))
def fixDown (n r : Nat) : Nat := bif Nat.ble (Nat.mul r r) n then r else Nat.sub r 1
/-- candidate floor sqrt for `n >= 1`: Newton from `2^(floor(log2 n)/2 + 1) >= sqrt n` -/
def isqrtC (n : Nat) : Nat := fixDown n (newton8 n (Nat.shiftLeft 1 (Nat.add (Nat.shiftRight (lg_0_512 n) 1) 1)))
/-- `s^2 <= n < (s+1)^2` -/
def isFloorSqrt (n s : Nat) : Bool := Nat.ble (Nat.mul s s) n && Nat.ble (Nat.add n 1) (Nat.mul (Nat.add s 1) (Nat.add s 1))
def isqrtChk (n s : Nat) : Nat := bif isFloorSqrt n s then s else 0
/-- floor sqrt (checked; 0, a sound lower bound, if the check fails) -/
def isqrtLo (n : Nat) : Nat := isqrtChk n (isqrtC n)
/-- `2^178 >= floor(sqrt m)` for every `m < 2^356` (the fallback that keeps the static bound chain) -/
def SQF : Nat := 383123885216472214589586756787577295904684780545900544
/-- floor sqrt of `m >= n` from `s = isqrt n` (`s^2 <= n`): `s` or `s+1` when `m < (s+1)^2` or `m < (s+2)^2`
(exact, since `s^2 <= m`), else recomputed and checked; the fallback is the constant 2^178 >= sqrt m for every
m < 2^356: a sound upper end that keeps the static bound chain -/
def isqrtHiF (m t : Nat) : Nat := bif isFloorSqrt m t then t else SQF
def isqrtNext (m s : Nat) : Nat :=
  bif Nat.ble (Nat.add m 1) (Nat.mul (Nat.add s 1) (Nat.add s 1)) then s
  else bif Nat.ble (Nat.add m 1) (Nat.mul (Nat.add s 2) (Nat.add s 2)) then Nat.add s 1
  else isqrtHiF m (isqrtC m)
def sqrt2 (a : DN) (sl : Nat) : DN :=
  ⟨Nat.add B sl, bif Nat.ble a.hi B then B else Nat.add (Nat.add B (isqrtNext (Nat.shiftLeft (Nat.sub a.hi B) 100) sl)) 1⟩
/-- lean/'s `sqrt` -/
def sqrt (a : DN) : DN := sqrt2 a (bif Nat.ble a.lo B then 0 else isqrtLo (Nat.shiftLeft (Nat.sub a.lo B) 100))

/-! ## Certain comparisons (as in lean/) -/
def ltc (a b : DN) : Bool := Nat.blt a.hi b.lo
def lec (a b : DN) : Bool := Nat.ble a.hi b.lo
def gec (a b : DN) : Bool := Nat.ble b.hi a.lo
def pos (a : DN) : Bool := Nat.blt B a.lo
def nonneg (a : DN) : Bool := Nat.ble B a.lo
def nonpos (a : DN) : Bool := Nat.ble a.hi B
/-- lean/'s `dabs` -/
def dabs (x : DN) : DN := bif Nat.ble B x.lo then x else bif Nat.ble x.hi B then neg x else ⟨B, nmax (Nat.sub B2 x.lo) x.hi⟩
end DN

/-- lean/'s `SQ3`, `TWO_OVER_SQ3_M1`, and `rho = DI.ofRat 2141 2500` -/
def SQ3 : DN := ⟨115792089237316195423570985008687907853269984667836199285298060769552899430151, 115792089237316195423570985008687907853269984667836199285298060769552899430152⟩
def TWO_OVER_SQ3_M1 : DN := ⟨115792089237316195423570985008687907853269984665836670269789672447509606294703, 115792089237316195423570985008687907853269984665836670269789672447509606294705⟩
def RHO : DN := ⟨115792089237316195423570985008687907853269984666726180013493039667354906265020, 115792089237316195423570985008687907853269984666726180013493039667354906265021⟩

end S43K

end
