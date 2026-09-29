import Proof.Rows.RowsPartsStep
import Proof.Rows.RowsAssemble

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.PartsFill
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_RowReady
open RowsConstruction.BaseLayout RowsConstruction.CompleteBank RowsConstruction.PartsStep
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. Budget monotonicity (to merge the initializer's and the row's `coefficient/degree`) -/

/-! ## 2. The uniform row fuel and `hbud` -/

/-! ## 3. The holes -/

/-! ## 4. `Parts` from the holes -/

end
end RowsConstruction.PartsFill
