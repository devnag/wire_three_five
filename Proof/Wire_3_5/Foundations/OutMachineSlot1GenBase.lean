import Proof.Wire_3_5.Foundations.OutMachineSlot1P

/-! # SA's slot 1, part 4: the writer, and SA from slot 0

* **`slot1W l : CoreWordsMJ l 1 (SA.slot1Ws l)`**: S4's word 1 (the sample word) at every request, one machine for
  every gate (capacity `28·(|fpIn|+1)`, steps and residues within `5000·(|fpIn|+1)^2`);
* **`saOf l slot0 : S4WordsMAJ l`**: SA from the offset's writer (slot 0), this writer and the carrier tables.

Paper quantity of the main type: S4's sample word (P3:3044-3048, 3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish

/-- The output stream as a one-word embedding. -/
def sOut1 : Fin 1 ↪ Fin 3 := ⟨fun _ => O, fun a b _ => Subsingleton.elim a b⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot1

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SA
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Finish

end NearCubicWires.WireExponent3_5.FinalPass.Out.SA
