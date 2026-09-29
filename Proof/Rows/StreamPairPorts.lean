import Proof.Rows.StreamPair

/-! Only the consumed stream/count/clock projections of the paired producer.
All other tapes remain opaque across the upcoming paid rewind. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_StreamPairPorts
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.VerifierDecoding SignedSortKey
open PCJ45bee56da9f34d5a_FourfoldBaseData (Data)
open PCJ45bee56da9f34d5a_StreamPair
noncomputable section



end
end PCJ45bee56da9f34d5a_StreamPairPorts
