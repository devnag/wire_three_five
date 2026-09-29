import Proof.CaseAnalysis.WitnessSumPrefix
import Proof.CaseAnalysis.WitnessSumBodyRun

/-! The complete sum prefix and term body share their actual field stream,
count driver and verdict. All other parser fields occupy one separate
reusable bank; the retained coefficient and native streams are untouched. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 528) : Fin 3061 :=
  ⟨if i.val=357 then 722 else if i.val=368 then 2532 else if i.val=499 then 724 else 2533+i.val,
    by split_ifs <;> omega⟩
noncomputable def reader := RecoveryFocus.machine slots SumPrefix.machine

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumDock
