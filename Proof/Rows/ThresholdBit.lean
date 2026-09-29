import Proof.Assembly.LiveRows
import Proof.Rows.FinalWalkStep
import Proof.Rows.SelectionWord

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_ThresholdBit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
open scoped BigOperators
noncomputable section

/-! ## 1. The shifted-target equation decides the residue, at ANY bit vector -/

/-! ## 2. The physical per-cell run -/

/-! ## 3. The bit is the printed cell of `gridWord` -/

end
end PCJ45bee56da9f34d5a_ThresholdBit
