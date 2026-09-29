import Proof.Wire_3_5.FinalPass.Close8
import Proof.Wire_3_5.Foundations.OutMachineSwLA

/-!
# The final pass's closure join, step 9

`finalPassClose8` with SW's templates supplied by verified code: `swLAll`
. The producers still open are SW's two remaining parts: `Pf` (flat tables) and `Pn` (numbers).

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
