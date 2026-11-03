import Lean
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The c4 leaf, module stage 1

This module collects the c4 leaf's first verified block: the SYM setup and its dock on the Stage3 wrapper at the
computed capacity, the wrapper and the per-mode assembly `c4Leaf_of`, and the C3 request writer `c3ReqLeaf2`. It proves
nothing new: the target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage1

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimT.SeedFixTypes.C4Leaf l

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ∀ l : Literals, PrimT.SeedFixTypes.C4Leaf l := h

end NearCubicWires.WireExponent3_5.C4Stage1

end
