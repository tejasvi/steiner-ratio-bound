import S43Core.Check

/-! # Replay of the compact DFS code stream

The certificate of a case is one binary tree over `[0, inf)^nb`. Its top levels are fixed: the `nb` splits at 1 that make
the root boxes (variable `i` in `[1, inf)` if bit `i` of the root number is set, else `[0, 1]`; `walkTop`). Below a root,
the data is a stream of codes in DFS order: an internal node splitting variable `k` is the byte `'!' + k` (lower half
first); a leaf is `'p' + lemma` (`'y'` = lemma -1) followed by the split id in two base-64 digits `48 + v`. Every box is
recomputed from the codes (exact midpoints; an infinite side `[lo, inf)` splits at `2 lo`, and at `1` if `lo = 0`), so the
stream is untrusted: a malformed stream makes the walk fail. Every leaf is checked by `checkRecord`. -/

namespace S43

/-- the code stream as a byte function with its length -/
structure Codes where
  get : Nat → Nat
  size : Nat

def Codes.ofBytes (b : ByteArray) : Codes := ⟨fun i => (b.get! i).toNat, b.size⟩

/-- the code stream of a data string (7-bit characters) -/
def Codes.ofString (s : String) : Codes := Codes.ofBytes s.toUTF8

/-- the two halves of a box along variable k, or `none` if the midpoint is not exact / the side is degenerate -/
def halves (bx : Box) (k : Nat) : Option (Box × Box) :=
  if k ≥ bx.lo.size then none else
  let lo := bx.lo[k]!
  match bx.hi[k]! with
  | some h =>
    if (lo + h) % 2 != 0 || !(lo < h) then none
    else let m := (lo + h) / 2
      some (⟨bx.lo, bx.hi.set! k (some m)⟩, ⟨bx.lo.set! k m, bx.hi⟩)
  | none =>
    let m := if lo == 0 then (1 : Int) <<< P else 2 * lo
    if !(0 ≤ lo) then none
    else some (⟨bx.lo, bx.hi.set! k (some m)⟩, ⟨bx.lo.set! k m, bx.hi⟩)

/-- decode a leaf at position `i`: lemma id and split id -/
def leafAt (cs : Codes) (i : Nat) : Option (Int × Int) :=
  let c := cs.get i
  if 112 ≤ c && c ≤ 121 && i + 2 < cs.size then
    let lid : Int := if c == 121 then -1 else (c - 112 : Nat)
    let d1 := cs.get (i + 1); let d2 := cs.get (i + 2)
    if d1 < 48 || d1 ≥ 112 || d2 < 48 || d2 ≥ 112 then none
    else some (lid, ((d1 - 48) * 64 + (d2 - 48) : Nat))
  else none

/-- walk the subtree at position `i` with box `bx`; `some` (next position) iff every leaf passes (`fuel` bounds the
depth) -/
def walk (C : Case) (rho : DI) (cs : Codes) : Nat → Nat → Box → Option Nat
  | 0, _, _ => none
  | fuel + 1, i, bx =>
    if i ≥ cs.size then none else
    let c := cs.get i
    if 33 ≤ c && c < 33 + C.nb then
      match halves bx (c - 33) with
      | none => none
      | some (l, r) =>
        match walk C rho cs fuel (i + 1) l with
        | none => none
        | some i1 => walk C rho cs fuel i1 r
    else
      match leafAt cs i with
      | some (lid, sid) => if checkRecord C rho bx sid lid != .fail then some (i + 3) else none
      | none => none

/-- the whole domain `[0, inf)^nb` -/
def topBox (nb : Nat) : Box := ⟨Array.replicate nb 0, Array.replicate nb none⟩

/-- the fixed top levels: split variables `k - 1, ..., 0` at 1, then walk the root subtrees in order -/
def walkTop (C : Case) (rho : DI) (cs : Codes) (fuel : Nat) : Nat → Nat → Box → Option Nat
  | 0, i, bx => walk C rho cs fuel i bx
  | k + 1, i, bx =>
    match halves bx k with
    | none => none
    | some (l, r) =>
      match walkTop C rho cs fuel k i l with
      | none => none
      | some i1 => walkTop C rho cs fuel k i1 r

/-- the whole certificate of a case: every leaf passes and the stream is used up -/
def checkAll (C : Case) (rho : DI) (cs : Codes) : Bool :=
  walkTop C rho cs 200 C.nb 0 (topBox C.nb) == some cs.size

/-! ## Sharded certificates

The tree is cut into jobs (subtrees). The skeleton stream holds the top of the tree with `'z'` for each job; the jobs'
streams are concatenated, in order, into shard streams. `skelBoxes` recomputes the job boxes from the skeleton, and a shard
checks its jobs' subtrees from those boxes (the job streams carry no boxes). -/

def walkSkel (C : Case) (cs : Codes) : Nat → Nat → Box → Option (Nat × List Box)
  | 0, _, _ => none
  | fuel + 1, i, bx =>
    if i ≥ cs.size then none else
    let c := cs.get i
    if 33 ≤ c && c < 33 + C.nb then
      match halves bx (c - 33) with
      | none => none
      | some (l, r) =>
        match walkSkel C cs fuel (i + 1) l with
        | none => none
        | some (i1, b1) =>
          match walkSkel C cs fuel i1 r with
          | none => none
          | some (i2, b2) => some (i2, b1 ++ b2)
    else if c == 122 then some (i + 1, [bx])
    else none

def walkTopSkel (C : Case) (cs : Codes) (fuel : Nat) : Nat → Nat → Box → Option (Nat × List Box)
  | 0, i, bx => walkSkel C cs fuel i bx
  | k + 1, i, bx =>
    match halves bx k with
    | none => none
    | some (l, r) =>
      match walkTopSkel C cs fuel k i l with
      | none => none
      | some (i1, b1) =>
        match walkTopSkel C cs fuel k i1 r with
        | none => none
        | some (i2, b2) => some (i2, b1 ++ b2)

/-- the job boxes, in order (the skeleton stream must be used up) -/
def skelBoxes (C : Case) (cs : Codes) : Option (Array Box) :=
  match walkTopSkel C cs 200 C.nb 0 (topBox C.nb) with
  | some (i, bs) => if i == cs.size then some bs.toArray else none
  | none => none

/-- jobs `j, j + 1, ...` (`n` of them): their subtrees, one after the other from position `i`, all pass -/
def jobsOK (C : Case) (rho : DI) (cs : Codes) (bs : Array Box) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | n + 1, j, i =>
    match walk C rho cs 200 i bs[j]! with
    | none => false
    | some i' => jobsOK C rho cs bs n (j + 1) i'

/-- a shard: the `n` jobs from `j0` on, with their streams in `cs` -/
def shardOK (C : Case) (rho : DI) (skel cs : Codes) (j0 n : Nat) : Bool :=
  match skelBoxes C skel with
  | some bs => decide (j0 + n ≤ bs.size) && jobsOK C rho cs bs n j0 0
  | none => false

/-- the number of jobs -/
def skelSize (C : Case) (skel : Codes) : Nat := ((skelBoxes C skel).map Array.size).getD 0

/-- structural skip of a subtree: the position after it (nothing is checked) -/
def skipTree (C : Case) (cs : Codes) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, i =>
    if i ≥ cs.size then none else
    let c := cs.get i
    if 33 ≤ c && c < 33 + C.nb then
      match skipTree C cs fuel (i + 1) with
      | none => none
      | some i1 => skipTree C cs fuel i1
    else if 112 ≤ c && c ≤ 121 then some (i + 3) else none

/-- the start positions of `n` consecutive subtrees from position `i` -/
def jobStarts (C : Case) (cs : Codes) : Nat → Nat → Option (List Nat)
  | 0, _ => some []
  | n + 1, i =>
    match skipTree C cs 200 i with
    | none => none
    | some i' => (jobStarts C cs n i').map (i :: ·)

/-- a shard with its jobs checked in parallel tasks (the start positions only say where each job's walk begins; each
walk is checked on its own) -/
def shardOKPar (C : Case) (rho : DI) (skel cs : Codes) (j0 n : Nat) : Bool :=
  match skelBoxes C skel, jobStarts C cs n 0 with
  | some bs, some starts =>
    decide (j0 + n ≤ bs.size) && decide (starts.length = n) &&
      ((starts.zip (List.range n)).map fun p =>
        Task.spawn fun _ => (walk C rho cs 200 p.1 bs[j0 + p.2]!).isSome).all Task.get
  | _, _ => false

end S43
