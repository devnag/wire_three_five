import Proof.Packets.DeltaScalarFields
import Proof.Packets.PacketsXDeltaTargetGuard

/-! An executed complete delta metadata calculation. Retained unary masters
are split and framed physically; subtraction and both validity flags are
then computed on the resulting framed operands. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaMetadata
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open RecoveryRootRound SignedSortKey DeltaScalarFields
noncomputable section

def slots : Fin 15→Fin 25 := ![8,9,10,14,15,16,17,18,19,20,21,22,12,23,24]
def guard := RecoveryFocus.machine slots DeltaTargetGuard.machine
def machine := Composition.machine DeltaScalarFields.machine guard

end
end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaMetadata
