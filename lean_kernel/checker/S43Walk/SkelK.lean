module

public import S43CoreK.CheckK

@[expose] public section

/-! # Skeleton walk on Nat boxes (the box helpers `setN` / `setO` are used by the case walk)

The skeleton stream (lean/'s data/Ck/s/skel.txt: `'!' + k` = split variable k, `'z'` = a job) packed 32 seven-bit codes per
Nat (code i of a window at bits 7i..7i+6). `skelCount` replays lean/'s `walkTopSkel` (root splits at 1 for variables
nb-1, ..., 0, lower half first; lean/'s `halves` on the box) and counts the jobs; the boxes are computed exactly as lean/'s walk
does. -/

namespace S43K

/-- lean/'s `halves` on Nat boxes (lower ends `lo`, upper ends `hi`, `none` = +inf): the two halves along variable `k` -/
def setN : List Nat → Nat → Nat → List Nat
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, k + 1, v => x :: setN xs k v
def setO : List (Option Nat) → Nat → Option Nat → List (Option Nat)
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, k + 1, v => x :: setO xs k v
/-- midpoint of side k: exact half of a finite side (`none` if odd or degenerate), 2 lo (or 1) for an infinite side -/
def midK (l : Nat) : Option Nat → Option Nat
  | some h => bif Nat.blt l h && Nat.beq (Nat.mod (Nat.add l h) 2) 0 then some (Nat.div (Nat.add l h) 2) else none
  | none => some (bif Nat.beq l 0 then 1267650600228229401496703205376 else Nat.mul 2 l)

/-- the packed reader: current window, codes left in it, remaining windows -/
structure Rd where
  w : Nat
  c : Nat
  ws : List Nat

def rdGet : Rd → Option (Nat × Rd)
  | ⟨w, c + 1, ws⟩ => some (Nat.land w 127, ⟨Nat.shiftRight w 7, c, ws⟩)
  | ⟨_, 0, w :: ws⟩ => some (Nat.land w 127, ⟨Nat.shiftRight w 7, 31, ws⟩)
  | ⟨_, 0, []⟩ => none

/-- walk one skeleton subtree from box (lo, hi): `some (reader after it, job count)` (structural on fuel) -/
def skelSub (nb : Nat) : Nat → Rd → List Nat → List (Option Nat) → Option (Rd × Nat)
  | 0, _, _, _ => none
  | fuel + 1, r, lo, hi =>
    match rdGet r with
    | none => none
    | some (c, r') =>
      bif Nat.beq c 122 then some (r', 1)
      else bif Nat.ble 33 c && Nat.blt c (Nat.add 33 nb) then
        (match midK (lo.getD (Nat.sub c 33) 0) (hi.getD (Nat.sub c 33) none) with
         | none => none
         | some m =>
           match skelSub nb fuel r' lo (setO hi (Nat.sub c 33) (some m)) with
           | none => none
           | some (r1, n1) =>
             match skelSub nb fuel r1 (setN lo (Nat.sub c 33) m) hi with
             | none => none
             | some (r2, n2) => some (r2, Nat.add n1 n2))
      else none

/-- lean/'s `walkTopSkel`: the fixed top splits at 1 (variables k-1, ..., 0), then the skeleton subtrees -/
def skelTop (nb fuel : Nat) : Nat → Rd → List Nat → List (Option Nat) → Option (Rd × Nat)
  | 0, r, lo, hi => skelSub nb fuel r lo hi
  | k + 1, r, lo, hi =>
    match midK (lo.getD k 0) (hi.getD k none) with
    | none => none
    | some m =>
      match skelTop nb fuel k r lo (setO hi k (some m)) with
      | none => none
      | some (r1, n1) =>
        match skelTop nb fuel k r1 (setN lo k m) hi with
        | none => none
        | some (r2, n2) => some (r2, Nat.add n1 n2)

def skelCount (nb : Nat) (ws : List Nat) : Option Nat :=
  match skelTop nb 200 nb ⟨0, 0, ws⟩ (List.replicate nb 0) (List.replicate nb none) with
  | some (_, n) => some n
  | none => none

end S43K

end
