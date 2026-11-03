import Lean
import Proof.Wire_3_5.Assembly.HashStage1
import Proof.Wire_3_5.Primitive.Writers.HashLeaf4
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.UnionMachine.WalkStage
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.FiltPipeLe
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.HashFam4Base
import Proof.Wire_3_5.Primitive.Writers.HashLeafBase
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ShellH4Run
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPolyBase
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5


noncomputable section
set_option maxRecDepth 4096


/-!
# HASH writer: the leaf (finish term)

The hash writer at every literal set and every writer-side `PreLinkT` (P3:2220-2226, 3068-3084): the `hashLeaf4`
 applied to the extended data stage `thrStage4U`, C6's walk bank and FILTER setup (
), the FILTER-pipe bound `filtPipe_le2` and the THR number sizes `thrNumsPoly`.

Paper quantity of the main type: `HashLeafJ2 l`, the hash writer of the seed-fix stage.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.HashFinish

open NearCubicWires.WireExponent3_5

/-- **The HASH writer leaf.** -/
noncomputable def hashFinal : HashStage1.StageT :=
  fun l _ => PrimAsm.HashLeaf.hashLeaf4 l (PrimT.TS4.thrStage4U l) UnionMachine.WalkStage.walkBank
    (UnionMachine.FsSpec.fsSpec UnionMachine.WalkStage.walkBank) UnionMachine.FiltPipeLe.filtPipe_le2
    (PrimT.W6.thrNumsPoly l)

end NearCubicWires.WireExponent3_5.HashFinish

end
