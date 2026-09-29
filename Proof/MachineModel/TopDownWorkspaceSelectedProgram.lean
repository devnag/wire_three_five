import Proof.MachineModel.TopDownWorkspaceSelectedAdmission

/-! Actual guarded ProgramData with a caller-chosen fixed continuation tape
count. Admission preserves its original cache and initializes every added tape
to [] at head zero. The endpoint's admission_run field is supplied here; the
admitted continuation and Runtime remain the two substantive proof regions. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceSelectedProgram
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal
open RepairSource.CloseoutFinal.C10LengthGate (exitTapes)
open WorkspaceGuardedWorker (input entry reference)
open WorkspaceSelectedAdmission (originalTapes coldCutoff preFuel)
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.admission

def admission (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (extra : Nat) :=
  TapeEmbedding.machine extra (WorkspaceSelectedAdmission.admission sources p k clock)

end
end NearCubicWires.P1TopDown.WorkspaceSelectedProgram
