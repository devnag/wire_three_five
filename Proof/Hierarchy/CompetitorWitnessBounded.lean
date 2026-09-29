import Proof.Hierarchy.CompetitorWitnessBoundedLayout

/-! The actual all-input branch precedes the canonical header. Oversized
witnesses halt immediately after the linear cap guard; the nested parser is
entered only with the physical cap bit true. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev headerStates := Fintype.card (RecoveryCalls.Control CompetitorWitnessTriple.sizes)+
  Fintype.card (RecoveryCalls.Control CompetitorWitnessHeader.sizes)
def sizes : Fin 2→ℕ := ![36,headerStates]
noncomputable def programs : (j : Fin 2)→Machine 150 (sizes j)
  | ⟨0,_⟩=>cap
  | ⟨1,_⟩=>header
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (cells : Fin 150→Bool) : Option (Fin 2) :=
  if j.val=0 ∧ cells 148=true then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
