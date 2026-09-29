import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Primitive.Writers.ShellH4Run

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.HashStage1

open NearCubicWires.WireExponent3_5

/-- The HASH writer leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.HashLeafJ2 l

def pass (h : StageT) : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.HashLeafJ2 l := h

end NearCubicWires.WireExponent3_5.HashStage1
