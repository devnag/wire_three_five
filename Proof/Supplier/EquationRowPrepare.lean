import Proof.Supplier.EquationRowAllocate
import Proof.Supplier.EquationRowPhiHeader
import Proof.Supplier.EquationIdentityColumns

/-! From the original framed row alone, prepare the exact reusable cut-loop
workspace and physically advance its three sentinel-count heads. The output header
then receives its φ part for the identity instance, `natWord d` and the identity columns
(paper3 alg:pullback, P3:1623-1671, with φ = id), on retained all-false tapes only. -/
namespace NearCubicWires.RepairOrdinary.EquationRowPrepare
open LocalBitMultitape RecoveryExecution RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 126) : Prop := i=34 ∨ i=38 ∨ i=40
instance (i : Fin 126) : Decidable (selected i) := inferInstanceAs (Decidable (i=34 ∨ i=38 ∨ i=40))
def boot : Machine 126 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,fun _ => none,fun i => if selected i then .right else .stay⟩

noncomputable def first := TapeEmbedding.machine 15 EquationHeaderCold.machine
noncomputable def allocated := Composition.machine first EquationRowAllocate.machine
noncomputable def booted := Composition.machine allocated boot
noncomputable def erased := Composition.machine booted EquationRowPhiHeader.erase
noncomputable def appended := Composition.machine erased EquationRowPhiHeader.append
noncomputable def machine := Composition.machine appended
  (RecoveryFocus.machine EquationRowPhiHeader.writerSlots EquationIdentityColumns.machine)

end NearCubicWires.RepairOrdinary.EquationRowPrepare
