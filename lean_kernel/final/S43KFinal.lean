module

public import AggLibK
public import S43KAgg.C1.Root
public import S43KAgg.C2.Root
public import S43KAgg.C3.Root
public import S43KAgg.C4.Root

/-! # The Steiner ratio is at least 2141/2500 (kernel-only proof)

The two theorems of `S43/Statements.lean` (here its module copy, which differs only by the module header), proved with
no native code: every record of the certificate is checked by the kernel (the units, `decide +kernel` on the kernel
checker `checkRecordK`), the units are chained per case by the aggregators into
`S43KAgg.Ck.Root.root : ChainK k (rootStackK k) []`, and the proof chain (K0-K4, AggLibK) turns the four roots into
lean/'s `CaseOK`s, hence `certificate` and `steiner_ratio_ge`. Case `k` is lean/'s numbering:
C1 = d_regular f ≥ d, C2 = d_steiner f := d, C3 = d_regular f ≤ d, C4 = d_steiner f ≤ d. -/

namespace S43K.Final

open S43.Stmt

public theorem certificate (F : Fam) (w : Vars) (hw : domain F w) :
    ∃ sp ∈ splits F, ∃ L ≤ 8, certifies F sp L (2141 / 2500) w :=
  S43K.certificateK_roots S43KAgg.C1.Root.root S43KAgg.C2.Root.root S43KAgg.C3.Root.root S43KAgg.C4.Root.root F w hw

public theorem steiner_ratio_ge (Real : Realized) (H : LemmaLayer Real) :
    ∀ P : Finset ℂ, (2141 / 2500 : ℝ) * mstLength P ≤ steinerLength P :=
  S43K.steiner_ratio_geK_roots S43KAgg.C1.Root.root S43KAgg.C2.Root.root S43KAgg.C3.Root.root S43KAgg.C4.Root.root Real H

example : type_of% @certificate = type_of% @Cert.certificate := rfl
example : type_of% @steiner_ratio_ge = type_of% @Main.steiner_ratio_ge := rfl

end S43K.Final
