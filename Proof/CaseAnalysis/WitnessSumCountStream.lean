import Proof.CaseAnalysis.WitnessSumGuard
import Proof.CaseAnalysis.RowsCircuitCountHeader

/-! Emit the actual guarded per-sum term count once. The native count
stream delimits the unchanged coefficient and circuit streams in variable
order; the producer directly aliases the retained count at sum port504. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCountStream
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 19) : Fin 528 :=
  ⟨if i.val=0 then 504 else if i.val=17 then 526 else if i.val=18 then 527 else 509+i.val,by split_ifs <;> omega⟩
noncomputable def machine := RecoveryFocus.machine slots CloseoutRowsCircuitCountHeader.machine

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCountStream
