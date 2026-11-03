import Lean
import Proof.Wire_3_5.Assembly.HashStage1
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.HashFam4Base
import Proof.Wire_3_5.Primitive.Writers.HashLeafBase
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.Primitive.Writers.ShellH4Run


noncomputable section
set_option maxRecDepth 4096


/-!
# HASH writer, module stage 2

The second verified block of the hash writer: the `hashLeaf4` with its closure beyond stage 1. It proves nothing new:
the target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `HashLeafJ2 l`, the hash writer of the seed-fix stage (P3:2220-2226, 3068-3084).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.HashStage2

open NearCubicWires.WireExponent3_5

/-- The HASH writer leaf, unchanged (an alias). -/
abbrev StageT : Type := HashStage1.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : HashStage1.StageT := h

end NearCubicWires.WireExponent3_5.HashStage2

end
