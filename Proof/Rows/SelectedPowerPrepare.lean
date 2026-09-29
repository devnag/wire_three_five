import Proof.Rows.SelectedPowerBody

/-! The selected coefficient cell's arity comes from the actual TOP payload;
its child-index driver comes from the retained private framed binary digit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerPrepare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
noncomputable section

def bank (a B p w F U n index v key : Nat) (source out : List Bool):Fin 101→List Bool:=
 Fin.addCases (m:=99) (n:=2) (motive:=fun _=>List Bool)
  (PCJ45bee56da9f34d5a_SelectedPowerBank.bank a B p w F U n index source [] out)
  ![frame (binary v key),List.replicate v true]



end
end PCJ45bee56da9f34d5a_SelectedPowerPrepare
