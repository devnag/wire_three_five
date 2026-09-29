import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.FinalPass.SdCtr1

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage2

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage1.StageT

def pass (h : StageT) : FinalPassStage1.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage2
