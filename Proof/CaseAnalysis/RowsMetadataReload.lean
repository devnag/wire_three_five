import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.Amplification.RecoveryCursorCalls
import Proof.Amplification.RecoveryRowLookupTapes
import Proof.Hierarchy.HierarchyAllocation

/-! Six existing bounded-copy calls reload exactly the degree worker's
short metadata. Native row heads and the accumulated output cursor remain
at their physical positions. The C driver and log are shared and retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsMetadataReload
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def dest : Fin 6→Fin 112 := ![51,52,61,66,89,90]
def source (i : Fin 6) : Fin 112 := i.natAdd 106
def slots (j : Fin 6) : Fin 4→Fin 112 := ![source j,dest j,104,105]
def sizes : Fin 6→ℕ := fun _=>4
noncomputable def programs (j : Fin 6) : Machine 112 (sizes j) :=
  RecoveryFocus.machine (slots j) RecoveryBoundedTapeCopy.machine
def next (j : Fin 6) (_q : Fin (sizes j)) (_bits : Fin 112→Bool) : Option (Fin 6) :=
  if h : j.val<5 then some ⟨j.val+1,by omega⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next


end NearCubicWires.RepairOrdinary.CloseoutRowsMetadataReload
