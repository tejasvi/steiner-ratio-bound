module

public import S43Walk.WalkK

@[expose] public section

/-! # The case walk as a FOLD over one merged code stream

The merged stream of a case is, job after job: the skeleton codes since the previous job (`'!' + k` splits the top box
of the skeleton stack, lower half on top), the job's `'z'`, then the job's subtree codes (`'!' + k` splits the top box
of the job stack; a leaf `'p' + L` or `'y'` followed by two base-64 digits pops it and emits a record). State: the two
explicit DFS stacks. The whole case is `walkFold` from `⟨rootSt, []⟩` to `⟨[], []⟩` over the concatenated stream; a
data unit is the fold over its slice between two stack literals (the chain is checked by the case glue). Boxes at scale
2^-40 (`midW`), records lifted by `up60` in the record theorems. Structural recursion on the code list. -/

namespace S43K

structure WSt where
  sk : List BoxS
  js : List BoxS
  deriving DecidableEq

def isSplit (nb c : Nat) : Bool := Nat.ble 33 c && Nat.blt c (Nat.add 33 nb)
def isLeafC (c : Nat) : Bool := Nat.ble 112 c && Nat.ble c 121
def isDigit (d : Nat) : Bool := Nat.ble 48 d && Nat.blt d 112

/-- the two halves of box `b` along variable `k` at midpoint `m`, lower half first (lean/'s `halves`) -/
def halfLo (b : BoxS) (k m : Nat) : BoxS := ⟨b.lo, setO b.hi k (some m)⟩
def halfHi (b : BoxS) (k m : Nat) : BoxS := ⟨setN b.lo k m, b.hi⟩

def walkFold (nb : Nat) : List Nat → WSt → List RecK → Option (WSt × List RecK)
  | [], st, acc => some (st, acc)
  | c :: cs, ⟨b :: sk, []⟩, acc =>
    bif Nat.beq c 122 then walkFold nb cs ⟨sk, [b]⟩ acc
    else bif isSplit nb c then
      (match midW (b.lo.getD (Nat.sub c 33) 0) (b.hi.getD (Nat.sub c 33) none) with
       | none => none
       | some m => walkFold nb cs ⟨halfLo b (Nat.sub c 33) m :: halfHi b (Nat.sub c 33) m :: sk, []⟩ acc)
    else none
  | c :: cs, ⟨sk, b :: js⟩, acc =>
    bif isSplit nb c then
      (match midW (b.lo.getD (Nat.sub c 33) 0) (b.hi.getD (Nat.sub c 33) none) with
       | none => none
       | some m => walkFold nb cs ⟨sk, halfLo b (Nat.sub c 33) m :: halfHi b (Nat.sub c 33) m :: js⟩ acc)
    else bif isLeafC c then
      (match cs with
       | d1 :: d2 :: cs' =>
         bif isDigit d1 && isDigit d2 then
           walkFold nb cs' ⟨sk, js⟩
             (⟨b.lo, b.hi, Nat.add (Nat.mul (Nat.sub d1 48) 64) (Nat.sub d2 48), bif Nat.beq c 121 then 9 else Nat.sub c 112⟩ :: acc)
         else none
       | _ => none)
    else none
  | _ :: _, ⟨[], []⟩, _ => none

/-- unpack 32 seven-bit codes per Nat -/
def unpack32 (w : Nat) : Nat → List Nat → List Nat
  | 0, rest => rest
  | k + 1, rest => Nat.land w 127 :: unpack32 (Nat.shiftRight w 7) k rest
def unpack : List Nat → List Nat
  | [] => []
  | w :: ws => unpack32 w 32 (unpack ws)

/-- a unit's claim: its `n` codes take the skeleton stack `startSk` (job stack empty) to `endSk` (job stack empty),
emitting `recsRev` (reverse order) -/
def unitWalkOK (nb : Nat) (ws : List Nat) (n : Nat) (startSk endSk : List BoxS) (recsRev : List RecK) : Bool :=
  match walkFold nb ((unpack ws).take n) ⟨startSk, []⟩ [] with
  | some (st, acc) => decide (st = ⟨endSk, []⟩) && decide (acc = recsRev)
  | none => false

/-- `P` holds for every record of the list (core-only `List.Forall`) -/
def ForallR (P : RecK → Prop) : List RecK → Prop
  | [] => True
  | r :: rs => P r ∧ ForallR P rs

/-- the record predicate of a unit: the record, lifted to scale 2^-100, does not fail -/
def recOK (st : Bool) (fval nb : Nat) (r : RecK) : Prop :=
  S43K.checkRecordK st fval nb ⟨up60 r.lo, up60o r.hi⟩ r.sid r.lid ≠ .fail

/-- a unit's exported claim: some code slice takes the skeleton
stack `startSk` to `endSk` and every record it emits passes -/
def UnitClaim (st : Bool) (fval nb : Nat) (startSk endSk : List BoxS) : Prop :=
  ∃ ws n recsRev, unitWalkOK nb ws n startSk endSk recsRev = true ∧ ForallR (recOK st fval nb) recsRev

end S43K

end
