import Proof.CaseAnalysis.WitnessFamilyFields

/-! The canonical exact-V header shares the actual family source,
repeat driver and verdict with the complete family loop. Its fixed
private bank is retained outside that loop without a second traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 177) : Fin 3241 :=
  ⟨if i.val=30 then 3061 else if i.val=41 then 3063 else if i.val=172 then 724 else 3064+i.val,
    by split_ifs <;> omega⟩
noncomputable def reader:=RecoveryFocus.machine slots FamilyCount.machine


end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyDock
