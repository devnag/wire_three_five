import Lean
import Proof.Wire_3_5.FinalPass.Close8
import Proof.Wire_3_5.Foundations.OutMachineSwLA
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SWParts
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.Foundations.OutMachineHUBase
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Foundations.OutMachineNwBVBase
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase
import Proof.Wire_3_5.Foundations.OutMachineSwLABase
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
# The final pass's closure join, step 9

`finalPassClose8` with SW's templates supplied by verified code: X6's `swLAll`.
The producers still open are SW's two remaining parts: `Pf` (flat tables) and `Pn` (numbers).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close9

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The final pass from SW's two remaining parts.** -/
noncomputable def finalPassClose9 (Pf : ∀ l, SWParts.SWfT l) (Pn : ∀ l, SWParts.SWnT l) :
    FinalPassStage1.StageT :=
  Close8.finalPassClose8 Pf Out.SwL.swLAll Pn

end NearCubicWires.WireExponent3_5.FinalPass.Close9

end
