module

public import S43Walk.SkelK

@[expose] public section

/-! # Helpers of the case walk S43Walk.WalkK2 (midW, up60, up60o, RecK, BoxS), plus an earlier per-module slice walk
(leafK, jobWalk, sliceWalk, walkOK) that no unit uses

Boxes are kept at scale 2^-40 (small literals: Lean's Nat hash is the low 64 bits, so 2^-100-scale dyadics would all
collide in the kernel cache); the record theorems lift them with `up60`. The slice walk replays, from an explicit DFS
stack of pending boxes, the skeleton slice (codes `'!'+k` split the top box of the stack, lower half on top; `'z'` pops a
job box) and, for every job, its subtree in the job stream (lean/'s `walk`: `'!'+k` splits, `'p'+L` / `'y'`
+ two base-64 digits = a leaf), collecting the leaves' (box, split id, lemma id) in reverse order. Decoding only: no
evaluation here. -/

namespace S43K

/-- lean/'s `halves` midpoint at the walk's scale 2^-40 (box ends of the certificate are dyadics of resolution >= 2^-9 in all
samples; a finer end would make this fail, never pass): exact half of a finite side, 2 lo (or 1.0) for an infinite one -/
def midW (l : Nat) : Option Nat → Option Nat
  | some h => bif Nat.blt l h && Nat.beq (Nat.mod (Nat.add l h) 2) 0 then some (Nat.div (Nat.add l h) 2) else none
  | none => some (bif Nat.beq l 0 then 1099511627776 else Nat.mul 2 l)

/-- lift a walk box end (scale 2^-40) to the checker's scale 2^-100 -/
def up60 : List Nat → List Nat
  | [] => []
  | x :: xs => Nat.shiftLeft x 60 :: up60 xs
def up60o : List (Option Nat) → List (Option Nat)
  | [] => []
  | none :: xs => none :: up60o xs
  | some x :: xs => some (Nat.shiftLeft x 60) :: up60o xs

structure RecK where
  lo : List Nat
  hi : List (Option Nat)
  sid : Nat
  lid : Nat
  deriving DecidableEq

structure BoxS where
  lo : List Nat
  hi : List (Option Nat)
  deriving DecidableEq

/-- the leaf at the reader: `'p' + L` (L = 0..9) or `'y'` (L = -1, stored as 9 like the record modules), two digits -/
def leafK (c : Nat) (r : Rd) : Option (Nat × Nat × Rd) :=
  match rdGet r with
  | none => none
  | some (d1, r1) =>
    match rdGet r1 with
    | none => none
    | some (d2, r2) =>
      bif Nat.ble 48 d1 && Nat.blt d1 112 && Nat.ble 48 d2 && Nat.blt d2 112 then
        some (bif Nat.beq c 121 then 9 else Nat.sub c 112, Nat.add (Nat.mul (Nat.sub d1 48) 64) (Nat.sub d2 48), r2)
      else none

/-- one job subtree from box (lo, hi): `some (reader after it, leaves prepended to acc)` -/
def jobWalk (nb : Nat) : Nat → Rd → List Nat → List (Option Nat) → List RecK → Option (Rd × List RecK)
  | 0, _, _, _, _ => none
  | fuel + 1, r, lo, hi, acc =>
    match rdGet r with
    | none => none
    | some (c, r') =>
      bif Nat.ble 33 c && Nat.blt c (Nat.add 33 nb) then
        (match midW (lo.getD (Nat.sub c 33) 0) (hi.getD (Nat.sub c 33) none) with
         | none => none
         | some m =>
           match jobWalk nb fuel r' lo (setO hi (Nat.sub c 33) (some m)) acc with
           | none => none
           | some (r1, acc1) => jobWalk nb fuel r1 (setN lo (Nat.sub c 33) m) hi acc1)
      else bif Nat.ble 112 c && Nat.ble c 121 then
        (match leafK c r' with
         | none => none
         | some (lid, sid, r2) => some (r2, ⟨lo, hi, sid, lid⟩ :: acc))
      else none

/-- the skeleton slice from a DFS stack: process skeleton codes until `n` jobs have been walked -/
def sliceWalk (nb : Nat) : Nat → Nat → Rd → Rd → List BoxS → List RecK → Option (List BoxS × List RecK)
  | 0, _, _, _, _, _ => none
  | _, 0, _, _, st, acc => some (st, acc)
  | fuel + 1, n + 1, sk, jr, b :: st, acc =>
    match rdGet sk with
    | none => none
    | some (c, sk') =>
      bif Nat.beq c 122 then
        (match jobWalk nb 200 jr b.lo b.hi acc with
         | none => none
         | some (jr', acc') => sliceWalk nb fuel n sk' jr' st acc')
      else bif Nat.ble 33 c && Nat.blt c (Nat.add 33 nb) then
        (match midW (b.lo.getD (Nat.sub c 33) 0) (b.hi.getD (Nat.sub c 33) none) with
         | none => none
         | some m => sliceWalk nb fuel (n + 1) sk' jr (⟨b.lo, setO b.hi (Nat.sub c 33) (some m)⟩ ::
                       ⟨setN b.lo (Nat.sub c 33) m, b.hi⟩ :: st) acc)
      else none
  | _, _, _, _, [], _ => none

/-- the walk claim of a module: from `start`, `n` jobs, the job stream used up exactly, ending at `endSt`, with the
leaves `recsRev` (reverse order) -/
def walkOK (nb fuel n : Nat) (skel jobs : List Nat) (start endSt : List BoxS) (recsRev : List RecK) : Bool :=
  match sliceWalk nb fuel n ⟨0, 0, skel⟩ ⟨0, 0, jobs⟩ start [] with
  | some (st, acc) => decide (st = endSt) && decide (acc = recsRev)
  | none => false

end S43K

end
