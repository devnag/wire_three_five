import Proof.Rows.RowsThrCell
import Proof.Rows.SelectionWord
import Proof.MachineModel.BlockLoop

/-! # Rows C3(d), part 2: the whole THR selection mask of one external row

**Consumer.** Warm field 2 of the row's `datumFields` is `gridWord live s harity row.select`
(`SelectionWord.mask_cells_printerPoint`, `…_SelectionWord.lean:108`; `warmFields_selection` `:141`).
For a THR row `row.select z = decide (modularOffset occ live (joinInput live (fun _ => false) z)
(equation a r sel) p = o)` (`Packets.thrFamily`, `fixed-live-packet-parent-20260921/PCJ9eff70d512234a4c_Packets.lean:74`).
`thr_mask` below appends EXACTLY that word to the verdict tape, from resident masters, in
`printerPoint` order, by one fixed machine (two nested `Cells` loops over `RowsThrCell.body`).

**Paper.** `paper.tex:1190-1212`: "One external row … is charged one complete `2^{q-K}`-column score
table." Budget class: TABLE — `2^((s+1)/2)` outer iterations of `2^(s/2)` cells, each cell a cost
polynomial in the request (`R`, `Bt`, `q`, `s`); nothing of `copyCap`, `smallSize` or `2^K` is multiplied
into it. Both cursors return to 0 and both loop counters are restored, so the loop is re-entrant.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrMask
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution SignedSortKey
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.BlockPlatform NearCubicWires.SupplierEstimator RowsConstruction.ThrCell
noncomputable section

/-! ## 0. Flat enumeration = rows of columns -/

/-! ## 1. A loop's receipt as a `Step` -/

/-! ## 2. The row-cursor increment (on the cell layout) -/


/-! ## 3. The two loops -/

end
end RowsConstruction.ThrMask
