import Proof.CaseAnalysis.WitnessMassCapacity
import Proof.CaseAnalysis.RowsGateSourceCalls

/-! The combined term verdict is folded before either exit. True commits
the same coefficient; false only clears the parser. No rejected term reaches
mass arithmetic or retained-record emission. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermExit
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flagSlots : Fin 2→Fin 827:=![719,724]
noncomputable def foldFlag:=RecoveryFocus.machine flagSlots CloseoutRowsIntegerRound.flagMachine
private def stateCount {s : ℕ} (_ : Machine 827 s):=s
noncomputable def sizes : Fin 3→ℕ:=![2,stateCount TermCommit.machine,stateCount TermCommit.erase]
noncomputable def programs : (j : Fin 3)→Machine 827 (sizes j)
  | 0=>foldFlag
  | 1=>TermCommit.machine
  | 2=>TermCommit.erase
def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 827→Bool) : Option (Fin 3):=
  if j.val=0 then if bits 719 then some 1 else some 2 else none
noncomputable def machine:=RecoveryCalls.machine sizes programs 0 next

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermExit
