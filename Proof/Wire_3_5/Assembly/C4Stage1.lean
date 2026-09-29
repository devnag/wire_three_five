import Proof.Wire_3_5.Primitive.SeedFix.C4KLeaf
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWF
import Proof.Wire_3_5.Primitive.Writers.C3WLeaf

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage1

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimT.SeedFixTypes.C4Leaf l

def pass (h : StageT) : ∀ l : Literals, PrimT.SeedFixTypes.C4Leaf l := h

end NearCubicWires.WireExponent3_5.C4Stage1
