import Proof.Wire_3_5.FinalPass.Core11Base

/-! # S5Core, part 13: the writers' stages (P3:3044-3048, 3170-3181)

* **`stageABN`**: S4's words part A (slots `0 … 3`), part B (slots `4 … 7`) and the numbers (`tN`, `tD`) written by
  their machine writers (`wstage`), the room invariant moved to the SYM block, the reference, the mode tape and every
  other tape kept;
* **`stageS`**: the branch on the mode tape: at a SYM request the SYM words written (`SymWordsM`), at a THR request
  nothing.

Paper quantities: S4's own words, the printed numbers' start, the SYM evaluator's call words (P3:3044-3048,
3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Run
variable {l : Literals} (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {mTh : ℕ}
 (L : S5Lay Sw0.nw) 

theorem outA_ne_outB (k k' : Fin 4) : outA L k ≠ outB L k' := fun e => by
  have := congrArg Fin.val (L.wdInj e); simp [s4SlotA, s4SlotB] at this; omega

theorem wd_ne_outN (k : Fin (17 + Sw0.nw)) (i : Fin 2) : L.wd k ≠ outN L i := by
  fin_cases i
  · exact L.wdN k
  · exact L.wdD k

theorem outS_ne_outA (k : Fin 17) (k' : Fin 4) : outS L k ≠ outA L k' := fun e => by
  have := congrArg Fin.val (L.wdInj e); simp [symSlot, s4SlotA] at this; omega

theorem outS_ne_outB (k : Fin 17) (k' : Fin 4) : outS L k ≠ outB L k' := fun e => by
  have := congrArg Fin.val (L.wdInj e); simp [symSlot, s4SlotB] at this; omega

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core
