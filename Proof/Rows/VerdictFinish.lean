import Proof.Rows.ThresholdTraversal

/-! Copy the actual verdict to the external table and erase the bounded
private bank. The table's existing prefix is outside every cleanup bound. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_VerdictFinish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.P1Closure
noncomputable section

def bank (A :Fin 254→List Bool) (R :Nat) (out :List Bool):Fin 257→List Bool:=
 Fin.addCases (m:=254) (n:=3) (motive:=fun _=>List Bool) A
  ![List.replicate R true,List.replicate (R+1) false,out]


end
end PCJ45bee56da9f34d5a_VerdictFinish
