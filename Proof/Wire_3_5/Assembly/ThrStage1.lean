import Lean
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.FinalPass.RadPreBase
import Proof.Wire_3_5.FinalPass.RadCaps
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.PreLink


noncomputable section
set_option maxRecDepth 4096


/-!
# The thr leaf, module stage 1

The first verified block of the thr leaf: the writers join and the thr leaf interface `ThrLeafOf4`, and the RADIX stage
7 (`RadReqB.Caps` and `Pre`), whose THR side conditions (the ThrSide chain) bring the THR mode's shared machinery. The
target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `ThrLeafJ2 l`, the THR writer of `lem:primitive` (P3:3011-3016, 3165-3175) at every
literal instance.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage1

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.ThrLeafJ2 l

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.ThrLeafJ2 l := h

end NearCubicWires.WireExponent3_5.ThrStage1

end
