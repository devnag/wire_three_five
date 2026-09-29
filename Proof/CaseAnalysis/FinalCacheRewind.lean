import Proof.CaseAnalysis.FinalCacheAtAdmission

/-! One paid cold rewind, starting with an empty recording log, followed by
fixed cache-head positioning. Every original cache byte and the admission flag
are preserved. This does not assume a preallocated rewind capacity. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheRewind

open NearCubicWires LocalBitMultitape ExtDecompositionBatch SourceInterfaces
open RepairSource RepairRepresentation ProjectionNormalization CloseoutWitness
open CloseoutFinalC10ColdCacheAtAdmission

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def machine {t s : ℕ} (p : Machine t s) := MaskedReset.machine p (fun _ => true)

attribute [local irreducible] BoundedFamilySupport.actualMachine ColdFamilySupport.actualMachine


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ColdCacheRewind
