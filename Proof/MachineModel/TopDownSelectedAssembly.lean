import Proof.MachineModel.TopDownWorkspaceSelectedProgram

/-! Substitute the actual admission into the literal endpoint. The complete
continuation program remains data, and its Verdict and Runtime remain open.
This is a checked reduction of the construction target, not a closed theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.SelectedAssembly
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes

structure ContinuationData (sources : EightSources) {gamma : Real}
    (p : Parameters sources gamma) where
  k : Nat
  clock : OrdinaryClock (fun n => n^(k+2))
  base : Nat
  extra : Nat
  states : Nat
  machine : LocalBitMultitape.Machine (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra) states
  result : Fin (WorkspaceSelectedAdmission.originalTapes sources p k+1+1+extra)
  fuel : Nat → Nat

def programData {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : ContinuationData sources p) : GuardedAssembly.ProgramData :=
  WorkspaceSelectedProgram.programData sources p C.k C.clock C.base C.extra C.machine C.result C.fuel

end
end NearCubicWires.P1TopDown.SelectedAssembly
