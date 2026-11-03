import Proof.Rows.CircuitPowerInput

/-! A complete reusable selected coefficient call from the actual outer TOP
frame and one private binary digit, with paid extraction and payload cleanup. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitPowerRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
open PCJ45bee56da9f34d5a_CircuitPowerInput
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section

def budget {n :Nat} (words :List (List Bool)) (circuit :Fin words.length) (C :Nat)
 (gs :List (ExactThresholdGate n)) (i :Fin gs.length) (w F U v :Nat):=
 (PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit C+4*U+12)+1+
 PCJ45bee56da9f34d5a_SelectedPowerReady.budget gs i w F U v+1+(2*U+4)

end
end PCJ45bee56da9f34d5a_CircuitPowerRun
