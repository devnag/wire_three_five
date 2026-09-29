import Proof.Supplier.RowNativeFieldSkip
import Proof.Circuits.DecompositionCachedChildAccess

/-! Physical access to a weight or the target of the selected native child.
Coordinates retain occurrence order, with the target at the actual arity. -/
namespace NearCubicWires.RepairOrdinary.RowNativeCoordinate
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields {n : ℕ} (g : ExactThresholdGate n) := List.ofFn g.weight++[g.target]
theorem word_fields {n : ℕ} (g : ExactThresholdGate n) : exactWord g=(fields g).flatMap intWord := by
  simp [fields,exactWord]

noncomputable def machine := RowNativeFieldSkip.loop

end NearCubicWires.RepairOrdinary.RowNativeCoordinate
