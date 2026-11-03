import Lean
import Proof.Wire_3_5.FinalPass.Stage2
import Proof.Wire_3_5.FinalPass.SdI10Base
import Proof.Wire_3_5.FinalPass.AssemblyDock2
import Proof.Wire_3_5.FinalPass.SdCtr1
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12


noncomputable section
set_option maxRecDepth 4096


/-!
# The final pass, module stage 3

The third verified block of the final pass: the seeds phase's instance `Sd.seedsWS2Of` with the S4 prep/setup/loop
machinery and the v4 seams with `OutMachine2` and `finalPass_of3`. The target passes through unchanged under the alias
`StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3046-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage3

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage2.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : FinalPassStage2.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage3

end
