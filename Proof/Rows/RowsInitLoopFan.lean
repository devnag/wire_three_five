import Proof.Rows.RowsInitMasterFan
import Proof.MachineModel.NativeFanout

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.LoopFan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open RowsConstruction RowsConstruction.BaseLayout RowsInit.MasterFan
noncomputable section

section Thr

end Thr

/-! ## The fanout -/




end
end RowsInit.LoopFan
