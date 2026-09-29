import Proof.Wire_3_5.FinalPass.Close4
import Proof.Wire_3_5.FinalPass.Stage6
import Proof.Wire_3_5.Foundations.OutMachineCarGen
import Proof.Wire_3_5.Primitive.Writers.SBNumsF
import Proof.Wire_3_5.UnionMachine.DataDock
import Proof.Wire_3_5.UnionMachine.NumsC7

/-!
# The final pass, module stage 7

The seventh verified block of the final pass, shipped ahead of the finish: the relaxed writer contract (CoreIfaceMJ)
and the core half over it (CoreJ10–CoreJ18: `coreGenJ`), the closure join `finalPassClose4` (open: the four pool writers
and the uniformity bundle), the shared per-call data dock (DataDock), NW's phase interface v3 and phase (c) over it
(NumsPh3, NumsC7), SB's arithmetic (SBNumsA–F), and the carrier phase (CarM2b, CarKit, CarS, CarPipe, CarBound,
CarGen). The finish then ships only the four pool writers' remaining parts, the uniformity bundle and the
instantiation of `finalPassClose4`. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage7

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage6.StageT

def pass (h : StageT) : FinalPassStage6.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage7
