import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.CaseAnalysis.RowsModeElementaryReset
import Proof.Amplification.RecoveryCursorCalls
import Proof.Amplification.RecoveryRowLookupTapes
import Proof.Hierarchy.HierarchyAllocation

/-! Four existing bounded-copy calls reload the actual elementary worker's
width, bound and degree fields. The append cursor is retained. All four
masters are original numeric fields; the C driver pays every copied cell. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReload
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dest : Fin 4→Fin 52 := ![2,3,12,18]
def source (i : Fin 4) : Fin 52 := (i.natAdd 46).castAdd 2
def slots (j : Fin 4) : Fin 4→Fin 52 := ![source j,dest j,50,51]
def sizes : Fin 4→ℕ := fun _=>4
noncomputable def programs (j : Fin 4) : Machine 52 (sizes j) :=
  RecoveryFocus.machine (slots j) RecoveryBoundedTapeCopy.machine
def next (j : Fin 4) (_q : Fin (sizes j)) (_bits : Fin 52→Bool) : Option (Fin 4) :=
  if h : j.val<3 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

noncomputable def data (A : Fin 52→List Bool) (C : ℕ)
    (templates : Fin 4→List Bool) (done : ℕ) : Fin 52→List Bool := fun i=>
  match RecoveryFocus.pick dest i with
  | none=>A i
  | some j=>if j.val<done then ZeroPadding.pad C (templates j) else List.replicate C false


end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReload
