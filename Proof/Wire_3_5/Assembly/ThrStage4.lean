import Lean
import Proof.Wire_3_5.Assembly.ThrStage3
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.RadBW5
import Proof.Wire_3_5.FinalPass.RadBW6
import Proof.Wire_3_5.FinalPass.RadCaps
import Proof.Wire_3_5.FinalPass.RadPreBase
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.PreLinkBase
import Proof.Wire_3_5.Primitive.Writers.ShellT2
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF4
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ9Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltPipeLe
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.RadBnd
import Proof.Wire_3_5.UnionMachine.RadCnt
import Proof.Wire_3_5.UnionMachine.RadDigs
import Proof.Wire_3_5.UnionMachine.RadFields2
import Proof.Wire_3_5.UnionMachine.RadFieldsP
import Proof.Wire_3_5.UnionMachine.RadNeed
import Proof.Wire_3_5.UnionMachine.RadNums
import Proof.Wire_3_5.UnionMachine.RadPipeB
import Proof.Wire_3_5.UnionMachine.RadScan
import Proof.Wire_3_5.UnionMachine.RadSeed
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.RadSpec3
import Proof.Wire_3_5.UnionMachine.RadTab
import Proof.Wire_3_5.UnionMachine.RadTrunc
import Proof.Wire_3_5.UnionMachine.RadWin
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5Base
import Proof.Wire_3_5.UnionMachine.ThrUnitOfBase
import Proof.Wire_3_5.UnionMachine.WalkStage
import Proof.Wire_3_5.UnionMachine.ThrDimCBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The thr leaf, module stage 4

The fourth verified block of the thr leaf: the completed THR decode front (ThrDecQ1–Q10: the quasi calculus, the call
atoms, the front's cost, the index links, `thrDecFront` and the uniform family `decT` at the cells `xT`), the THR
dimension-stage bounds (ThrDimM/N/C/G, `thrDimStageG`), and the closure join `thrClose2` (its one open argument is the
THR writer's tail). The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}`
(P3:3011-3016, 3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage4

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ThrStage3.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ThrStage3.StageT := h

end NearCubicWires.WireExponent3_5.ThrStage4

end
