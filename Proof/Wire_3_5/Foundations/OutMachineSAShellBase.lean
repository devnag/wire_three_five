import Proof.Wire_3_5.Foundations.OutMachineJoinWBase
import Proof.Wire_3_5.Foundations.OutMachineCarGenBase

/-! # SA's shell: S4's words 0–3 from their writers

S4's first four words at a request (`frontWordsW2 … (s4SlotA k)`, P3:3044-3048, 3170-3181): the offset word, the
sample word, the two carrier tables. SA is the join of three writers:

* **`slot0Ws`**, **`slot1Ws`** (the offset's and the sample's word families; `slot0Ws_eq`: the offset word
  `frameP (List.ofFn (C4Geo.offset P σ)) ++ [false]` at the call's star parameters and translation);
* `carF`, **`carSub l`** (`carPhaseJ l` at words 0–1, the carrier tables; `fw_car`: they are S4's words 2–3);
* **`saWords`** (the joined family is S4's words 0–3), **`saOf2`**, **`saOf`**-to-be:
  `saOf2 slot0 slot1 := ((slot0.join slot1).join (carSub l)).congrWs (saWords l) : S4WordsMAJ l`.

Paper quantity of the main type: S4's words (the offset, the sample, the carrier tables; P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish

variable (l : Literals)

/-- The carrier tables: the carrier phase's words `0`, `1`. -/
def carF : Fin 2 ↪ Fin 5 := Fin.castLEEmb (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.Out.SA
