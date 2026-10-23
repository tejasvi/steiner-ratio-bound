import S43Core.Splits
open S43
def badLines (txt : String) : Nat :=
  ((txt.splitOn "\n").filter (fun l => !(parseNats l).isEmpty)).foldl
    (fun n l => if (parseSplit (parseNats l)).isSome then n else n + 1) 0
def nonEmpty (txt : String) : Nat := ((txt.splitOn "\n").filter (fun l => !(parseNats l).isEmpty)).length
#eval (badLines numTextReg, nonEmpty numTextReg, badLines numTextSt, nonEmpty numTextSt)
