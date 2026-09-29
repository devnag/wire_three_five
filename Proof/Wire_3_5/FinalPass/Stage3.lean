import Proof.Wire_3_5.FinalPass.Stage2
import Proof.Wire_3_5.FinalPass.SdI11
import Proof.Wire_3_5.FinalPass.AssemblyDock3

/-!
# The final pass, module stage 3

The third verified block of the final pass: the seeds phase's instance `Sd.seedsWS2Of` with the S4 prep/setup/loop
machinery and the v4 seams with `OutMachine2` and `finalPass_of3`. It ships
ahead of the finish so that the finish ships only the output machine, the S5 halves, BridgeT, S6 and the assembly. The target passes
through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3046-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage3

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage2.StageT

def pass (h : StageT) : FinalPassStage2.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage3
