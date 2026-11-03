import Proof.Packets.FinalThresholdOneHotTargetArithmetic
import Proof.Rows.PhysicalFocusBoundary
import Proof.MachineModel.ClosureLocalSupport

/-! Both actual sign/range flags for a delta window target. The total residue
is produced even outside the valid range; the two physical flags select the
provider versus the physically generated zero polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaTargetGuard
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

def compareSlots : Fin 4→Fin 15 := ![10,12,13,14]
def machine := Composition.machine (TapeEmbedding.machine 3 C10ThresholdOneHotTargetArithmetic.machine)
  (RecoveryFocus.machine compareSlots CompetitorSignedDecision.compareMachine)


end
end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaTargetGuard
