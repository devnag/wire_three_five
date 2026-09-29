import Proof.Rows.MinimumMaskCell

/-! The actual q-counted native-sign pass builds the minimizing assignment.
Every weight is read in native order; the target suffix is never consumed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_MinimumMaskRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
open PCJ45bee56da9f34d5a_MinimumMaskCell
noncomputable section



def machine := RepeatMachine.machine PCJ45bee56da9f34d5a_MinimumMaskCell.machine (fun _ _ => true)

end
end PCJ45bee56da9f34d5a_MinimumMaskRun
