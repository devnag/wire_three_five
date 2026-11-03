import Proof.Supplier.RowTupleCursorLayout
import Proof.Supplier.RowTupleCursorErase
import Proof.Supplier.RowTupleCursorEquation

/-! A reusable whole-tuple body: the actual selected digits produce the
common-width equation, then paid erasure restores all per-tuple fields.
The stream cursor advances and the equation append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (F : ℕ) : Fin 48→ℕ := fun i=>if i=15 ∨ i=23 ∨ i=24 then F else 0
noncomputable def machine := Composition.machine RowTupleCursorEquation.machine RowTupleCursorErase.machine

end NearCubicWires.RepairOrdinary.RowTupleCursorBody
