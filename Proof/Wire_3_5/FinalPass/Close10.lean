import Proof.Wire_3_5.FinalPass.Close9
import Proof.Wire_3_5.FinalPass.SymF14

/-!
# The final pass's closure join, step 10

`finalPassClose9` with SW's flat tables supplied by verified code: `swf` at the walk bank
. The one producer still open is SW's last part `Pn` (the numbers).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close10

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The final pass from SW's numbers part.** -/
noncomputable def finalPassClose10 (Pn : ∀ l, SWParts.SWnT l) : FinalPassStage1.StageT :=
  Close9.finalPassClose9 (fun l => SymF.swf UnionMachine.WalkStage.walkBank l) Pn

end NearCubicWires.WireExponent3_5.FinalPass.Close10
