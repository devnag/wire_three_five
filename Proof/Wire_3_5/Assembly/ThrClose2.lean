import Lean
import Proof.Wire_3_5.Assembly.ThrClose
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ10
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.Assembly.ThrStage3
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5
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


noncomputable section
set_option maxRecDepth 120000


/-!
# The thr leaf's closure join, step 2

`thrClose` with the unit cells and the decode fronts supplied by verified code: the cells
`xT l F = max walkBank.x (dX …)` with `xT_walk`, and the decode fronts as a uniform family `decT`. The one
producer still open:

* `tail`: THRTAIL, the THR writer's leaf from the unit machines v4 (T-A = `ThrDimB.thrDimStageG`; T-B, the
  shell run and class link; the dock `thrLeafOfU4_of`), with the pre-link available.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3011-3016,
3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrClose2

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The thr leaf from exactly its remaining open producer**, THRTAIL. -/
noncomputable def thrClose2
    (tail : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → UnionMachine.ThrUnit.ThrLeafOfU4 l) :
    ThrStage3.StageT :=
  ThrClose.thrClose tail PrimT.ThrDecF.xT PrimT.ThrDecF.xT_walk PrimT.ThrDecF.decT

end NearCubicWires.WireExponent3_5.ThrClose2

end
