import Proof.MachineModel.OccurrenceRun

/-! Reuse the checked unary copier at a retained head-one template. Both
one-cell positioning moves are paid; zero uses the same construction. -/
namespace NearCubicWires.ExtDecompositionBatch.FinalUnary
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def position (forward : Bool) : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    ![if forward then .right else .left,.stay,.stay]⟩ else none

noncomputable def machine:=Composition.machine
  (Composition.machine (position false) (UWalkUnary.machine false false)) (position true)

end NearCubicWires.ExtDecompositionBatch.FinalUnary
