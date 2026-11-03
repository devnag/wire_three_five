import Proof.Rows.RowsThrSelBase

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.MaskStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open RowsConstruction.BaseLayout RowsConstruction.ThrCell
noncomputable section

/-! ## 1. The loop block -/


/-! ## 2. The local stage: loop block (`LT` tapes) + the two C6 words -/



end
end RowsConstruction.MaskStage
