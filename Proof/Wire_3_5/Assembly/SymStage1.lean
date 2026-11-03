import Lean
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Primitive.Writers.SymLeafIface
import Proof.Wire_3_5.Primitive.Writers.SymNums
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase


noncomputable section
set_option maxRecDepth 4096


/-!
# SYM writer, module stage 1

This module collects one verified block, the SYM per-call run `sym_ready`. It proves nothing new: the target passes
through unchanged under the alias `StageT`.

Paper quantity of the main type: `SymLeafJ2 l`, the SYM writer of the seed-fix stage (P3:3011-3016, 3105-3115).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SymStage1

open NearCubicWires.WireExponent3_5

/-- The SYM writer leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.SymLeafJ2 l

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.SymLeafJ2 l := h

end NearCubicWires.WireExponent3_5.SymStage1

end
