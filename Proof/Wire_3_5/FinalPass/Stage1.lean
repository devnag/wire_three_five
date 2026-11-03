import Lean
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.PlanBase


noncomputable section
set_option maxRecDepth 4096


/-!
# Final pass, module stage 1

This module collects one verified block: the SYM per-point evaluator S3 (`PrimT.S3.symPtEval`). It proves nothing new:
the target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage1

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.Plan.FinalPassLeaf l

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ∀ l : Literals, PrimAsm.Plan.FinalPassLeaf l := h

end NearCubicWires.WireExponent3_5.FinalPassStage1

end
