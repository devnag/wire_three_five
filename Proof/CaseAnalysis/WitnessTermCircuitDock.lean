import Proof.CaseAnalysis.WitnessTermCircuitReset

/-! The circuit reader directly aliases the retained term payload and
shared internal driver. Every other term/mass field remains outside its
bank; the supplied receipt is the actual circuit call, not a new parser. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitDock
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 1703) : Fin 2532 :=
  ⟨if i.val=1 then 78 else if i.val=1694 then 720 else 827+i.val,by split_ifs <;> omega⟩

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitDock
