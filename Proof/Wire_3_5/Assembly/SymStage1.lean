import Proof.Wire_3_5.Primitive.Writers.SymReady

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SymStage1

open NearCubicWires.WireExponent3_5

/-- The SYM writer leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.SymLeafJ2 l

def pass (h : StageT) : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.SymLeafJ2 l := h

end NearCubicWires.WireExponent3_5.SymStage1
