import Lean
import Proof.Wire_3_5.Assembly.ThrStage2
import Proof.Wire_3_5.UnionMachine.ThrUnitOfBase
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.UnionMachine.RadNeed
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.UnionMachine.RadBnd
import Proof.Wire_3_5.UnionMachine.RadPipeB
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecF4
import Proof.Wire_3_5.Primitive.Writers.ShellT2
import Proof.Wire_3_5.Primitive.Writers.SymDecEmit
import Proof.Wire_3_5.FinalPass.RadBW5
import Proof.Wire_3_5.FinalPass.RadBW6
import Proof.Wire_3_5.FinalPass.RadCaps
import Proof.Wire_3_5.FinalPass.RadPreBase
import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.UnionMachine.RadCnt
import Proof.Wire_3_5.UnionMachine.RadDigs
import Proof.Wire_3_5.UnionMachine.RadFields2
import Proof.Wire_3_5.UnionMachine.RadFieldsP
import Proof.Wire_3_5.UnionMachine.RadNums
import Proof.Wire_3_5.UnionMachine.RadScan
import Proof.Wire_3_5.UnionMachine.RadSeed
import Proof.Wire_3_5.UnionMachine.RadSpec3
import Proof.Wire_3_5.UnionMachine.RadTab
import Proof.Wire_3_5.UnionMachine.RadTrunc
import Proof.Wire_3_5.UnionMachine.RadWin


noncomputable section
set_option maxRecDepth 4096


/-!
# The thr leaf, module stage 3

The third verified block of the thr leaf: the RADIX setup instance and the THR unit machine with its measure (RadTrunc2
… RadBnd, RadPipeB, RadAsm0–5, RadLink/RadCall, the v2–v5 setup/unit interfaces, RadNeed/RadSetupRun,
UnitG/FiltLift/ThrPipes/ThrUnitRun, ThrUnitMeas/2/3, ThrUnitOf), T3's THR decode front so far (ThrDecA–E, R1–R9, F1–F4)
and the THR tail interface and its first lemmas (ThrDimIface, ThrTail0/1). The target passes through unchanged under the
alias `StageT`.

Paper quantity of the main type: `ThrLeafJ2 l`, the THR writer of `lem:primitive` (P3:3011-3016, 3165-3175) at every
literal instance.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage3

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ThrStage2.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ThrStage2.StageT := h

end NearCubicWires.WireExponent3_5.ThrStage3

end
