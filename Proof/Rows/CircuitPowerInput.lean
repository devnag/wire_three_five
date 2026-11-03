import Proof.Rows.SelectedPowerReady

/-! Extract one actual TOP circuit into the reusable coefficient cell. Only
payload94 is additionally padded; the growing coefficient stream is untouched. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitPowerInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopFrameReentry.machine

def caps (U :Nat) (i :Fin 101):=if i=94 then U else 0
def bank (a B p w F U v key circuit :Nat) (source payload out :List Bool):Fin 103→List Bool:=
 Fin.addCases (m:=101) (n:=2) (motive:=fun _=>List Bool)
  (fun i=>ZeroPadding.pad (caps U i) (PCJ45bee56da9f34d5a_SelectedPowerPrepare.bank a B p w F U 0 0 v key payload out i))
  ![frame source,ZeroPadding.pad U (CompareMachine.word circuit)]


end
end PCJ45bee56da9f34d5a_CircuitPowerInput
