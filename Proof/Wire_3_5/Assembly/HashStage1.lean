import Lean
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Primitive.Writers.ShellH4Run
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase


noncomputable section
set_option maxRecDepth 4096


/-!
# HASH writer, module stage 1

This module collects one verified block, the THR shell's run on the extended data stage `shell_runH4`. It proves nothing
new: the target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `HashLeafJ2 l`, the hash writer of the seed-fix stage (P3:2220-2226, 3068-3084).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.HashStage1

open NearCubicWires.WireExponent3_5

/-- The HASH writer leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.HashLeafJ2 l

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.HashLeafJ2 l := h

end NearCubicWires.WireExponent3_5.HashStage1

end
