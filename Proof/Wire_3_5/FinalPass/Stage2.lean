import Lean
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.FinalPass.SdCtr1
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 2

This module collects its first verified block: the seed-loop counters `SdCtr1` with the per-point THR evaluator chain
and the digit and row machines below it. It proves nothing new: the target passes through unchanged under the alias
`StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3046-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage2

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage1.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage1.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage2

end
