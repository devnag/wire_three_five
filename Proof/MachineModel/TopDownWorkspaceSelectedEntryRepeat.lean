import Proof.MachineModel.TopDownWorkspaceSelectedEntryReady

/-! The actual initialized source count drives the existing clause Repeat.
Its final false cell is retained physically. The local body layout and its
round receipt remain explicit, while all tapes outside the focus are kept. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedEntryRepeat
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource CloseoutWitness RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open WorkspaceSelectedEntry (size)
noncomputable section

def slots {t B : Nat} (body : Fin B→Fin t) (driver : Fin t) : Fin (B+1)→Fin t :=
  Fin.addCases body (fun _ : Fin 1=>driver)


end
end NearCubicWires.P1TopDown.WorkspaceSelectedEntryRepeat
