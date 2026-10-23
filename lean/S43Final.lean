import S43.Sound.MainProof
import S43.Sound.Data
import S43Data.C1.Case
import S43Data.C2.Case
import S43Data.C3.Case
import S43Data.C4.Case

/-! # The Steiner ratio is at least 2141/2500

The two theorems of `S43/Statements.lean`, proved:

* `S43.Final.certificate` = `S43.Stmt.Cert.certificate`: every point of the two case domains has a published split whose
  bound at rho = 2141/2500 is `≤ 0`. From the four cases (`S43Data.Ck.case`: d_regular f ≥ d, d_steiner f ≥ d (f := d),
  d_regular f ≤ d, d_steiner f ≤ d), each from its skeleton and shards (`native_decide`) and the checker's soundness
  (`S43.Sound`).
* `S43.Final.steiner_ratio_ge` = `S43.Stmt.Main.steiner_ratio_ge`: `(2141/2500) L_MST ≤ L_SMT` for every finite point set,
  given the lemma layer (`LemmaLayer`: the trapped-point lemmas, the case domains, the Du-Hwang framework).

The `example`s check that the statements are, up to definitional equality, those of `S43/Statements.lean`. -/

namespace S43.Final

open S43 S43.Stmt

theorem sizes_st : sizeCheck .st = true := by native_decide
theorem sizes_reg : sizeCheck .reg = true := by native_decide

theorem certificate (F : Fam) (w : Vars) (hw : domain F w) :
    ∃ sp ∈ splits F, ∃ L ≤ 8, certifies F sp L (2141 / 2500) w :=
  certificate_of_cases S43Data.C4.case S43Data.C2.case S43Data.C3.case S43Data.C1.case F w hw

theorem steiner_ratio_ge (Real : Realized) (H : LemmaLayer Real) :
    ∀ P : Finset ℂ, (2141 / 2500 : ℝ) * mstLength P ≤ steinerLength P :=
  main_of_certificate (by norm_num) (fun F => by cases F; exacts [size_of_check sizes_reg, size_of_check sizes_st])
    certificate Real H.trap H.domain H.duHwang

example : type_of% @certificate = type_of% @Cert.certificate := rfl
example : type_of% @steiner_ratio_ge = type_of% @Main.steiner_ratio_ge := rfl

end S43.Final
