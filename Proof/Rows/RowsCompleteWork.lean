import Proof.Rows.RowsMaskStage

/-! # Rows `complete` on the work block: the row's mask (both modes) and the verdict erase

**Consumer.** `complete`'s work-block duties between the row-level stages (rows-rowlevel `rowLevel_step`, C6
`frame_step`): C3 — leave the family row's selection mask on the verdict tape (`thr_mask_work`/`sym_mask_work`, from
`base j`, all heads `0`); then, after C6 has placed it, restore the verdict tape to `0^(2^s)` (`erase_work`) so that C5
(`RowsThrC5.thr_c5` / RC5's SYM C5) reaches `base (j+1)` exactly.
**Machines.** `maskW M := RecoveryFocus.machine lslots (maskStage M)` (the loop block + the two C6 words docked on the
work block), `eraseW := RecoveryFocus.machine eslots (RecoveryScratchErase.resetMachine 1)` (driver = C6 `1^(2^s)`, log
= C6 `0^(2·2^s+1)`).
**Paper.** `paper.tex:1190-1212`. **Budget.** Once per row: the mask loop (table class, one `2^s` factor) + `O(2^s)`.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CompleteWork
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open RowsConstruction.BaseLayout RowsConstruction.ThrCell RowsConstruction.MaskStage
noncomputable section

/-! ## 1. Ports -/

section Ports

end Ports

/-! ## 2. The two stages on any work bank -/

/-! ## 3. THR and SYM rows -/

section Thr

end Thr

end
end RowsConstruction.CompleteWork
