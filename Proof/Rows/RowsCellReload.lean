import Proof.Rows.ThresholdTraversal

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CellReload
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. Layout -/



/-! ## 2. The fanout slots: masters, the 254 cell inputs, the clock (254), the log (255) -/


/-! ## 3. The three stages -/

/-! ## 4. Stage lemmas -/

end
end RowsConstruction.CellReload
