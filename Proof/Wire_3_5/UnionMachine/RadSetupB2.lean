import Proof.Wire_3_5.UnionMachine.RadSetupB
import Proof.Wire_3_5.Primitive.ThresholdWriter.TopFront

/-! # RADIX, Route B, entry v3: the setup's entry with the circuits' payloads (`RsIn3`, `RadSetupSpecB2`)

P3:2543-2551, 2585-2623. The RADIX row's digit populations (P3:2598-2599) come from the equation `L_g`, whose
coefficients are the children of each circuit's retained top gate under the decomposition algorithm (`TopFront.payOf`).
The algorithm's tape count (`TF3Pay.TT a + 1` of `Classical.choice …`) has no bound, so the front end cannot run inside
the setup's fixed cell layout; the unit chain runs it beside W6 and hands the payloads over.

* `sPayK i = 133 + i` (`i < 4`), `rAK = 432`;
* **`RsIn3`**: `RsIn2` plus circuit `i`'s payload on `133 + i` (blank for `i ≥ a'`, heads `0`) and `a'` in `432`
  (registers outside `250 … 399` and `410 … 432` zero);
* **`RadSetupSpecB2 x l F`**: `RadSetupB.RadSetupSpecB` at the entry `RsIn3`.

Paper quantity of the main type: the RADIX row's C2 request (`RadSetup.radReqOf`) with its row's capacities. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB

/-- Circuit `i`'s payload stream. -/
def sPayK (i : Fin 4) : Fin 161 := ⟨133 + i.val, by have := i.isLt; omega⟩

/-- The circuit count's register. -/
def rAK : Fin LNR := ⟨432, by decide⟩

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB2
