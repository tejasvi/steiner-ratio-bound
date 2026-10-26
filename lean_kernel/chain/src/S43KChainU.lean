module

public import S43Walk.WalkK2

@[expose] public section

/-! # The aggregators' chain predicate

Imports only the walk library (no Mathlib, none of lean/'s files), so the aggregators stay light. A case's
units, chained in stream order, give `ChainK k (rootStackK k) []`; the final file turns that into K3's `Transfer`
(`transfer_of_chainU`, by induction from `unit_transfer` and `transfer_trans`). Case `k` is lean/'s numbering
(S43Data.Ck.case): C1 = d_regular f ≥ d
(fval 3, 6 coordinates), C2 = d_steiner f := d (fval 2, 7), C3 = d_regular f ≤ d (fval 1, 6), C4 = d_steiner f ≤ d
(fval 1, 8). gen_agg options: --chain-fmt 'S43K.ChainK {k} {a} {b}' --trans 'S43K.chainK_trans'
--of-unit 'S43K.chainK_of_unit' --lib-import S43KChainU --root-fmt 'S43K.rootStackK {k}' --root-import S43KChainU
--end-fmt '[]' -/

namespace S43K

/-- `S` reaches `T` through unit claims chained in stream order -/
inductive ChainU (st : Bool) (fval nb : Nat) : List BoxS → List BoxS → Prop
  | unit {S T : List BoxS} : UnitClaim st fval nb S T → ChainU st fval nb S T
  | trans {S T U : List BoxS} : ChainU st fval nb S T → ChainU st fval nb T U → ChainU st fval nb S U

def stK : Nat → Bool
  | 2 => true
  | 4 => true
  | _ => false

def fvalK : Nat → Nat
  | 1 => 3
  | 2 => 2
  | _ => 1

def nbK : Nat → Nat
  | 1 => 6
  | 2 => 7
  | 3 => 6
  | _ => 8

def ChainK (k : Nat) (S T : List BoxS) : Prop := ChainU (stK k) (fvalK k) (nbK k) S T

/-- the root stack of case `k`: the one box `[0, ∞)^nb` -/
def rootStackK (k : Nat) : List BoxS := [⟨List.replicate (nbK k) 0, List.replicate (nbK k) none⟩]

theorem chainK_trans {k : Nat} {S T U : List BoxS} (h1 : ChainK k S T) (h2 : ChainK k T U) : ChainK k S U :=
  ChainU.trans h1 h2

theorem chainK_of_unit {k : Nat} {S T : List BoxS} (h : UnitClaim (stK k) (fvalK k) (nbK k) S T) : ChainK k S T :=
  ChainU.unit h

end S43K

end
