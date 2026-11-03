import Proof.Wire_3_5.FinalPass.SampPad
import Proof.Wire_3_5.Primitive.SeedFix.C4Child

/-! # The degenerate call's padded batch (mode-generic), part 2: the child expression's value

P3:3011-3016: the child expression `chV` (the printed objective's terms at a child prefix `p'`) at the
padded batch (`padBatch`, the constant row per entry, `R′ = 1`) has the same value at every atom valuation as at
`R = 0` with any batch (the empty entries): the degenerate call's objective is unchanged by the padding. From
`sampTerms_pad_eval`.

* **`chV_pad_eval`** (the v7 shape).

Paper quantity of the main type: the value of the printed objective at a degenerate call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SampShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT

/-- **The child expression's value is unchanged by the padding.** -/
theorem chV_pad_eval (P : Sampler.SeedParams) (nT : ℕ) (b : List SeedFix.SExpr) (p' : List Bool) (v : ℕ → Bool) :
    Shared.IntExpression.eval (C4Child.chV P nT 1 (C4Pad.padBatch (2 ^ P.kh) nT) p') v =
      Shared.IntExpression.eval (C4Child.chV P nT 0 b p') v :=
  sampTerms_pad_eval P nT b p'.length (SeedFix.listNum p') v

end NearCubicWires.WireExponent3_5.FinalPass.SampShape
