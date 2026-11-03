import Lean
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.FinalPass.MajMain
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.PlanBase


noncomputable section
set_option maxRecDepth 4096


/-! # Final pass: the leaf's enclosing term 

"At each of `2^{n−k}` columns, evaluate the reported lookup at these `Q` pairs [...] The final pass costs
`2^{n−k/4}n^{C_D}`" (P3:3046-3048, 3170-3181). PA's residual for the final pass is `FinalPassLeaf l`: after the
endpoint exponent `fe`, the floors `E₅`, `CD₅`; for every admissible `F`, a coefficient `c₅` and, at every clock and
source work, a `RewoundWordFunction` from `req.word ++ seedWord` to `ratWord (greedyValue)` within
`c₅·(pre + mainPass)(E₅)`.

This module is the enclosing term with the machine as a typed parameter: a `WordBlocks` family (one machine for all
requests, all heads back at `0`) at every call family gives the leaf (`finalPassLeaf_of`, by base's
`WordBlocks.toRewound`). The machine is the final pass's word program converted once at the top (root).

Paper quantity of the main type: the primitive's printed value `ratWord (greedyValue I alg req)` (`FinalPassAt`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Primitive NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

variable (l : Literals)

/-- The machine family the final pass must supply at one call family. -/
noncomputable abbrev FinalPassBlocks (F : GateFree l) (E₅ : Envelope) (c₅ kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : Type :=
  { W : WordBlocks {req : PrimRequest // (callInputs l F kclk coef A a ha).Call req}
      (fun r => r.1.word ++ seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1)
      (fun r => ratWord (SeedFix.greedyValue (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1))
      (fun r => c₅ * finalClasses E₅ r.1.n (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (((gate0 l F).budget kclk coef A a ha).psiOf r.1.n)) // ∀ r, W.exitH r = fun _ => 0 }

/-- **The final pass's leaf from its machines** (the enclosing term; the machines are the parameter `W`). -/
noncomputable def finalPassLeaf_of (E₅ : ℕ → Envelope) (CD₅ : ℕ → ℕ) (c₅ : (fe : ℕ) → GateFree l → ℕ)
    (W : ∀ (fe : ℕ) (F : GateFree l), F.filterErrDeg = fe → ClassLE (E₅ fe) F.E → CD₅ fe ≤ F.CD →
      ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FinalPassBlocks l F (E₅ fe) (c₅ fe F) kclk coef A a ha) :
    FinalPassLeaf l :=
  fun fe => ⟨E₅ fe, CD₅ fe, fun F hF hE hCD => ⟨c₅ fe F, fun kclk coef A a ha =>
    (W fe F hF hE hCD kclk coef A a ha).1.toRewound (W fe F hF hE hCD kclk coef A a ha).2⟩⟩

end NearCubicWires.WireExponent3_5.FinalPass.Top

end
