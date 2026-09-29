import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmFields
import Proof.Rows.ClosureOffsetMask
import Proof.Rows.FinalCoordinateBridge

/-!
# The per-row selection mask word, in the printer's own cell order

`PCJ38fbfed565f64139_Row.Frame.fields printer (Packets.datum a F g layout row hr facts)` is
`P1TopDownPaidReloadCore.input printer d.row d.C d.Q d.select`
(`PCJeb9c0f0306e9481c_FramingSpec.datumFields`), whose seven warm payload fields are
`CloseoutRowsEstimator.WarmFields.words d.row d.Q estimate 1 d.select`
(`Proof/MachineModel/TopDownPaidReloadCore.lean`).  Entry `2` of those words is the only large varying
one, and is the BARE (unframed) list

  `CompetitorCountMask.mask (CompetitorSelectedCells.cells row.odd (fun _ _ => 0) select)`
  (`Proof/CaseAnalysis/CloseoutRowsEstimatorWarmFields.lean`).

`gridWord` below names that word directly in the printer's own coordinates: one bit per residual
column, flat index `k` addressing printed row `k / 2^(s/2)` and printed column `k % 2^(s/2)`,
which is exactly `C10ExternalRowLoop.printerPoint`'s cell `(rowN, colN)`.  Its type mentions the
row's own `sel : BitInput liveᶜ.card → Bool` and `printerPoint`, so nothing that fails to
evaluate that selector at every residual column can inhabit it.

`mask_cells_printerPoint` is the cell-order lemma: it discharges the `odd`/`u` crop
(`CompetitorFinalTable.lowerColumn`, applied by `CompetitorSelectedCells.cells` when
`s % 2 = 1`) against the flat `2 ^ s` enumeration, so `gridWord` IS the payload field.

`gridWord_run` then observes that `P1Closure.OffsetMaskSymmetric.run`
(`Proof/Rows/ClosureOffsetMaskSymmetric.lean`) — a concrete four-tape comparison loop with
no machine-shaped hypotheses — ALREADY emits that word, at
`OffsetMask.budget (request.circuits.length * w) (2 ^ s) = 2^s * (4*(L*w)+7) + 3`,
once the row's selector is identified with `fun z => decide (offsetOf request liveScale z = f)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_SelectionWord
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.RepairOrdinary.CompetitorCountMask (mask)
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. The word -/

/-! ## 2. `gridWord` is the payload field -/

/-! ## 3. The existing producer already emits it -/

end
end PCJ45bee56da9f34d5a_SelectionWord
