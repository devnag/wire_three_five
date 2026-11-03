import Lean
import Proof.Wire_3_5.FinalPass.Close7
import Proof.Wire_3_5.Primitive.SeedFix.SWt5
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SWParts
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.Foundations.OutMachineHUBase
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Foundations.OutMachineNwBVBase
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase
import Proof.Wire_3_5.Primitive.Writers.SBCap3Base
import Proof.Wire_3_5.Primitive.Writers.SBInstBase
import Proof.Wire_3_5.Primitive.SeedFix.NwB15Base
import Proof.Wire_3_5.Primitive.SeedFix.SBIdBase
import Proof.Wire_3_5.Primitive.SeedFix.SWt5Base
import Proof.Wire_3_5.UnionMachine.NumsG2Base
import Proof.Wire_3_5.UnionMachine.NumsW2Base


noncomputable section
set_option maxRecDepth 120000


/-!
# The final pass's closure join, step 8

`finalPassClose7` with SW's top tables supplied by verified code: the `swT` at `x = DT + 7`.
The producers still open are SW's three remaining parts: `Pf` (flat tables), `Pl` (templates), `Pn`
(numbers).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close8

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The final pass from SW's three remaining parts.** -/
noncomputable def finalPassClose8
    (Pf : ∀ l, SWParts.SWfT l) (Pl : ∀ l, SWParts.SWlT l) (Pn : ∀ l, SWParts.SWnT l) :
    FinalPassStage1.StageT :=
  Close7.finalPassClose7 (fun l => PrimT.SWt.swT (UnionMachine.DataDock.DT + 7) le_rfl l) Pf Pl Pn

end NearCubicWires.WireExponent3_5.FinalPass.Close8

end
