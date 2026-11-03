import Proof.CaseAnalysis.FinalLegalAdmission
import Proof.CaseAnalysis.FinalCacheAtAdmission

/-! Checked admission-sensitive upper application. Rejected descriptions need
an actual rejecting run, never phase records or a decoder-fallback identity.
The physical rejected branch remains a separate ordinary-machine obligation.
No worker continuation or overall runtime bound is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.WorkspaceGuardedProbe
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal
open CloseoutWitness SourceInterfaces RepairRepresentation
open RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open RepairSource.CloseoutFinal.C10GuardedStageConsumer
open RepairSource.CloseoutFinal.C10Fusion
open RepairSource.CloseoutFinal.C10LengthGate (exitTapes)
noncomputable section
attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine

end
end NearCubicWires.P1TopDown.WorkspaceGuardedProbe
