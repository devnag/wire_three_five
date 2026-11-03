import Proof.Rows.SelectedPowerBody

/-! Actual selected TOP child to its scaled coefficient block, then factor
update and full native-buffer reuse. No selected coefficient stream is assumed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_SelectedPowerBank
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section

def budget {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w F U : Nat) :=
 (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+C10ThresholdSelectedChild.budget (gs.get i) U+4*U+13)+1+
 (PCJ45bee56da9f34d5a_NativeScaleEquation.budget n F w U (gs.get i).target+1+(1024*(w+1)^2+10*U+18*w+45))+1+(4*U+9)

end
end PCJ45bee56da9f34d5a_SelectedPowerRun
