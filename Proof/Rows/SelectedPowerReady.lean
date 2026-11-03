import Proof.Rows.SelectedPowerPrepare

/-! Actual TOP arity and private binary digit feed the selected coefficient
mapper; both unary drivers are then paid back to their reusable cold bank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
open PCJ45bee56da9f34d5a_SelectedPowerPrepare
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_HeaderRewind.clear


def budget {n :Nat} (gs :List (ExactThresholdGate n)) (i :Fin gs.length) (w F U v :Nat):=
 ((2*PCPPQueryNatural.budget n+4*U+10)+1+(MatrixUnaryTemplate.budget v i.val+2*U+5))+1+
 PCJ45bee56da9f34d5a_SelectedPowerRun.budget gs i w F U+1+(4*U+9)

end
end PCJ45bee56da9f34d5a_SelectedPowerReady
