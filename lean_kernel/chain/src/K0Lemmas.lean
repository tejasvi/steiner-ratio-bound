module

public import Batteries.Data.String.Lemmas
public import Std.Data.String.ToNat
-- module form: the legacy splitOn / splitOnAux bodies are not exposed by core; `import all` makes them visible here
import all Init.Data.String.Legacy

@[expose] public section

/-! # K0 lemmas: the legacy `String.splitOn` with a one-character separator, on `String.ofList`

Batteries proves `String.splitToList_of_valid` (split by a predicate) and leaves the
`splitOn` analog as a TODO. `splitOnAux_char_of_valid` is that analog for a one-character separator; its proof mirrors
Batteries' `String.splitAux_of_valid`. With `String.toNat?_eq_some_ofDigitChars` (core `Std.Data.String.ToNat`) this
turns the statement's `S43.parseSplits` on `String.ofList cs` into a list-level function that the kernel evaluates. -/

namespace S43K
open String

theorem get_ofList_singleton (c : Char) : Pos.Raw.get (ofList [c]) 0 = c :=
  get_of_valid [] [c]

theorem next_ofList_singleton (c : Char) : Pos.Raw.next (ofList [c]) 0 = ⟨c.utf8Size⟩ := by
  have h : Pos.Raw.next (ofList ([] ++ c :: [])) ⟨utf8Len []⟩ = ⟨utf8Len [] + c.utf8Size⟩ :=
    next_of_valid [] c []
  rw [show utf8Len [] + c.utf8Size = c.utf8Size from Nat.zero_add _] at h
  exact h

theorem splitOnAux_char_of_valid (c : Char) (l m r : List Char) (acc : List String) :
    splitOnAux (ofList (l ++ m ++ r)) (ofList [c]) ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == c) r m.reverse).map ofList := by
  unfold splitOnAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, get_ofList_singleton, next_ofList_singleton, Pos.Raw.unoffsetBy_zero]
  split
  · subst r
    simpa using extract_of_valid l m []
  · obtain ⟨d, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    have hg : Pos.Raw.get (ofList (l ++ (m ++ d :: r))) ⟨utf8Len l + utf8Len m⟩ = d := by
      simpa [-ofList_append] using get_of_valid (l ++ m) (d :: r)
    have hn : Pos.Raw.next (ofList (l ++ (m ++ d :: r))) ⟨utf8Len l + utf8Len m⟩ =
        ⟨utf8Len l + utf8Len m + d.utf8Size⟩ := by
      simpa [-ofList_append] using next_of_valid (l ++ m) d r
    have hx : Pos.Raw.extract (ofList (l ++ (m ++ d :: r))) ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ =
        ofList m := by
      simpa using extract_of_valid l m (d :: r)
    simp only [hg, hn]
    by_cases h : d = c
    · subst h
      have hu : (⟨utf8Len l + utf8Len m + d.utf8Size⟩ : Pos.Raw).unoffsetBy ⟨d.utf8Size⟩ =
          ⟨utf8Len l + utf8Len m⟩ := by
        ext; simp
      rw [hu, hx]
      simp
      simpa [Nat.add_assoc, List.splitOnPPrepend_cons_eq_ite] using
        splitOnAux_char_of_valid d (l ++ m ++ [d]) [] r (ofList m :: acc)
    · have hne : (d == c) = false := beq_false_of_ne h
      simp only [hne, Bool.false_eq_true, ite_false]
      simpa [List.splitOnPPrepend_cons_eq_ite, h, Nat.add_assoc] using
        splitOnAux_char_of_valid c l (m ++ [d]) r acc

theorem splitOn_ofList_char (cs : List Char) (c : Char) :
    (ofList cs).splitOn (ofList [c]) = (cs.splitOnP (· == c)).map ofList := by
  have hne : (ofList [c] == "") = false := by
    rw [beq_eq_false_iff_ne]; intro h; simpa using congrArg String.toList h
  simp only [splitOn, hne, Bool.false_eq_true, ite_false]
  simpa using splitOnAux_char_of_valid c [] [] cs []

theorem isEmpty_ofList (l : List Char) : (ofList l).isEmpty = l.isEmpty := by
  rw [Bool.eq_iff_iff, String.isEmpty_iff, List.isEmpty_iff]
  constructor
  · intro h; simpa using congrArg String.toList h
  · intro h; subst h; simp

/-- `String.toNat?` on a character list. The all-digit case is computed on the list; it is the only case the split data
reaches (every token is a non-empty digit string). -/
def toNatL? (l : List Char) : Option Nat :=
  if !l.isEmpty && l.all Char.isDigit then some (Nat.ofDigitChars 10 l 0) else (ofList l).toNat?

theorem toNat?_ofList (l : List Char) : (ofList l).toNat? = toNatL? l := by
  unfold toNatL?
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true] at h
    have hd : ∀ c ∈ (ofList l).toList, c.isDigit := by simpa using h.2
    have hne : ofList l ≠ "" := by
      intro he; apply h.1; simpa using congrArg String.toList he
    rw [String.toNat?_eq_some_ofDigitChars (String.isNat_of_isDigit hne hd), toList_ofList]
    congr 2
    apply List.filter_eq_self.2
    intro c hc
    have hc' := h.2 c hc
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact absurd hc' (by decide)
  · rfl

end S43K

end
