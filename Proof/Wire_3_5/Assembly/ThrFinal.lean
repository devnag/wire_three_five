import Lean
import Proof.Wire_3_5.Assembly.ThrStage4
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB8
import Proof.Wire_3_5.Assembly.ThrClose2
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
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB6Base
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
import Proof.Wire_3_5.UnionMachine.ThrDimCBase
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5Base
import Proof.Wire_3_5.UnionMachine.ThrUnitOfBase
import Proof.Wire_3_5.UnionMachine.WalkStage


noncomputable section
set_option maxRecDepth 120000


/-!
# The thr leaf

The THR writer's leaf at every literal instance: root's closure join `thrClose2` (the verified decode fronts `decT` at
the cells `xT`, the unit machines `thrUnitOf5` over the RADIX setups `radStage`, the FILTER setup `fsSpec` at the walk
bank, the v4 data stage `thrStage4U`) applied to THRTAIL's `tail`: the shell run over the dimension stage with C6b's
bounds (`thrDimStageG`), the class link into the preprocessing class, and the v4 dock.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}`
(P3:3011-3016, 3094-3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrFinal

open NearCubicWires.WireExponent3_5

/-- **The thr leaf** at every literal instance. -/
noncomputable def thrFinal : ThrStage4.StageT :=
  ThrClose2.thrClose2 PrimT.ThrTB.tail

end NearCubicWires.WireExponent3_5.ThrFinal

end
