import Proof.Wire_3_5.Primitive.SeedFix.S3Big12

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage1

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.Plan.FinalPassLeaf l

def pass (h : StageT) : ∀ l : Literals, PrimAsm.Plan.FinalPassLeaf l := h

end NearCubicWires.WireExponent3_5.FinalPassStage1
