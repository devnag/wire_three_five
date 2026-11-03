import Lean
import Proof.Wire_3_5.Assembly.ThrStage1
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadDigs
import Proof.Wire_3_5.UnionMachine.RadWin
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.UnionMachine.RadFieldsP
import Proof.Wire_3_5.UnionMachine.RadFields2
import Proof.Wire_3_5.UnionMachine.RadNums
import Proof.Wire_3_5.UnionMachine.RadScan
import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.RadSpec3
import Proof.Wire_3_5.UnionMachine.RadSeed
import Proof.Wire_3_5.UnionMachine.RadTab
import Proof.Wire_3_5.UnionMachine.RadCnt
import Proof.Wire_3_5.UnionMachine.RadTrunc
import Proof.Wire_3_5.FinalPass.RadBW5
import Proof.Wire_3_5.FinalPass.RadBW6
import Proof.Wire_3_5.FinalPass.RadCaps
import Proof.Wire_3_5.FinalPass.RadPreBase
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5


noncomputable section
set_option maxRecDepth 4096


/-!
# The thr leaf, module stage 2

The second verified block of the thr leaf: the Route-B RADIX types and setup pieces (RadSetupB/B2/B3, RadSpec/2/3,
RadScan, RadNums, RadFields/2/P, RadDigs, RadWin, RadSeed, RadTab, RadCnt, RadTrunc), the THR unit-chain decode contract
`ThrDecFront`, and the RADIX block writer. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `ThrLeafJ2 l`, the THR writer of `lem:primitive` (P3:3011-3016, 3165-3175) at every
literal instance.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage2

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ThrStage1.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ThrStage1.StageT := h

end NearCubicWires.WireExponent3_5.ThrStage2

end
