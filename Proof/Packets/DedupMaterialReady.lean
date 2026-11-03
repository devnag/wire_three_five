import Proof.PCP.ProjectionNormalizationDedupReady

/-! Cold keep-last deduplication with both retained source and output banks
positioned at their starts, and both actual unary count drivers at position1.
All cursor changes are performed by the concrete reset and advance machines. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DedupMaterialReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

def nop : Machine 12 1 where
  descriptionBits := 0
  start := 0
  halted := fun _=>true
  rule := fun _ _=>none
noncomputable def stage := Composition.machine DedupCold.machine nop

def selected (i : Fin 12) := decide (i=0 ∨ i=2 ∨ i=3 ∨ i=11)
noncomputable def reset := MaskedReset.machine stage selected

def advance : Machine 13 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun _=>none,fun i=>if i=3 ∨ i=11 then .right else .stay⟩ else none
noncomputable def machine := Composition.machine reset advance

end PCJ9eff70d512234a4c_Fixed.Materializer.DedupMaterialReady
