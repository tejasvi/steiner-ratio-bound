module

public import Lean
public import S43Core.Splits
public import K0Lemmas
public import K0Lits
-- module form: `decide +kernel` below evaluates core's List.splitOnP and Nat.ofDigitChars, whose bodies core does not
-- expose; `import all` makes them visible here
import all Init.Data.List.SplitOn.Basic
import all Init.Data.Nat.ToString

@[expose] public section

/-! # K0 bridge: the statement's split lists equal explicit literals, proved in the kernel

The statement's files define `S43.splitsSt := parseSplits numTextSt`. It parses a 59,402-byte String with the
legacy `String.splitOn`, which the kernel cannot evaluate at that size. Steps (the statement's files stay unchanged):
1. `numTextSt = String.ofList csSt`, with `csSt` the literal's character list (`str_chars%`, `#str_eq`; the proof
   `Eq.refl` is checked by the kernel only).
2. `parseSplits (String.ofList cs) = (parseSplitsL cs).toArray` (`parseSplits_ofList`, by the lemmas of `K0Lemmas`).
3. `parseSplitsL csSt = splitsLitStL` by `decide +kernel`. The same for the regular family. -/

open Lean Elab Term Meta

set_option maxRecDepth 100000

/-- The characters of the String literal that defines the constant `c`, as the explicit list `[Char.ofNat n₁, …]`. -/
elab "str_chars% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some (.defnInfo d) := (← getEnv).find? n | throwError "not a definition"
  let .lit (.strVal s) := d.value.consumeMData | throwError "not a String literal"
  let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``Char)
  return s.toList.reverse.foldl (fun acc ch => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) (Lean.mkConst ``Char)
    (mkApp (Lean.mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)) acc) nil

/-- `#str_eq thm s cs`: adds `theorem thm : s = String.ofList cs` (for a String literal constant `s` and `cs` its
character list), with the proof `Eq.refl s` checked by the kernel only. -/
elab "#str_eq " thm:ident s:ident cs:ident : command => Command.liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo s
  let m ← realizeGlobalConstNoOverloadWithInfo cs
  let str := Lean.mkConst ``String
  let ty := mkApp3 (Lean.mkConst ``Eq [Level.one]) str (Lean.mkConst n)
    (mkApp (Lean.mkConst ``String.ofList) (Lean.mkConst m))
  let pf := mkApp2 (Lean.mkConst ``Eq.refl [Level.one]) str (Lean.mkConst n)
  addDecl (.thmDecl { name := (← getCurrNamespace) ++ thm.getId, levelParams := [], type := ty, value := pf })

namespace S43K
open String

deriving instance DecidableEq for S43.Split

/-- `S43.parseNats` on a character list. -/
def parseNatsL (l : List Char) : List Nat :=
  (l.splitOnP (· == ' ')).filterMap (fun t => if t.isEmpty then none else toNatL? t)

theorem parseNats_ofList (l : List Char) : S43.parseNats (ofList l) = parseNatsL l := by
  have hs : (" " : String) = ofList [' '] := rfl
  rw [S43.parseNats, hs, splitOn_ofList_char, List.filterMap_map]
  unfold parseNatsL
  congr 1
  funext t
  simp only [Function.comp_apply, isEmpty_ofList, toNat?_ofList]

/-- `S43.parseSplits` on a character list, as a list. -/
def parseSplitsL (cs : List Char) : List S43.Split :=
  ((cs.splitOnP (· == '\n')).filter (fun l => !(parseNatsL l).isEmpty)).map
    (fun l => (S43.parseSplit (parseNatsL l)).getD default)

theorem parseSplits_ofList (cs : List Char) :
    S43.parseSplits (ofList cs) = (parseSplitsL cs).toArray := by
  have hn : ("\n" : String) = ofList ['\n'] := rfl
  rw [S43.parseSplits, hn, splitOn_ofList_char]
  unfold parseSplitsL
  simp only [List.filter_map, List.map_toArray, List.map_map, Function.comp_def, parseNats_ofList]

noncomputable def csReg : List Char := str_chars% S43.numTextReg
noncomputable def csSt : List Char := str_chars% S43.numTextSt

set_option profiler true
set_option profiler.threshold 20

#str_eq numTextReg_eq S43.numTextReg csReg
#str_eq numTextSt_eq S43.numTextSt csSt

theorem parseSplitsL_reg : parseSplitsL csReg = splitsLitRegL := by decide +kernel

theorem parseSplitsL_st : parseSplitsL csSt = splitsLitStL := by decide +kernel

set_option profiler false

/-- K0, regular family: the statement's split list is the literal `splitsLitRegL`. -/
theorem splitsReg_eq : S43.splitsReg = splitsLitRegL.toArray := by
  rw [show S43.splitsReg = S43.parseSplits S43.numTextReg from rfl, numTextReg_eq, parseSplits_ofList,
    parseSplitsL_reg]

/-- K0, Steiner family: the statement's split list is the literal `splitsLitStL`. -/
theorem splitsSt_eq : S43.splitsSt = splitsLitStL.toArray := by
  rw [show S43.splitsSt = S43.parseSplits S43.numTextSt from rfl, numTextSt_eq, parseSplits_ofList,
    parseSplitsL_st]

end S43K

#print axioms S43K.splitsReg_eq
#print axioms S43K.splitsSt_eq

end
