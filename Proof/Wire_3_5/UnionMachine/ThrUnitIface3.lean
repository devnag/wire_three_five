import Lean
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.RadSetupB4
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Proof.Wire_3_5.UnionMachine.ThrUnitIface
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
import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.UnionMachine.RadSpecBase
import Proof.Wire_3_5.UnionMachine.ThrDecIfaceBase
import Proof.Wire_3_5.UnionMachine.RadSetupB5


noncomputable section
set_option maxRecDepth 4096


/-! # The producer statement over the RADIX setup v5 (#198 follow-up)

`ThrUnit.ThrUnitOf2` (M68) takes the RADIX setups as `RadSetupB4.RadSetupSpecB4`, whose measure misses the star row at
`G = 0`; the v5 setup `RadSetupB5.RadSetupSpecB5` adds it. The consumer types (`ThrUnitSpec2`, `ThrUnitU2`,
`ThrLeafOfU2`) are unchanged.

* `radDeg5`, `radCf5`, **`ThrUnitOf3 l`**: the uniform decode fronts, the uniform RADIX setups v5, the FILTER setup and its
  pipe bound give the unit machines v2.

Paper quantity of the main type: the THR tape's units within the preprocessing class `2^{O(Ψ)}` (P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm

/-- The RADIX setup v5's exponents and coefficients. -/
def radDeg5 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB5.RadSetupSpecB5 x l F) : ℕ :=
  max (max R.Dn R.Db) R.Dp

def radCf5 {x : ℕ} {l : Literals} {F : GateFree l} (R : RadSetupB5.RadSetupSpecB5 x l F) : ℕ := R.Kn + R.Kb + R.Kp

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit

end
