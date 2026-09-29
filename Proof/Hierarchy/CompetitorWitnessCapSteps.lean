import Proof.Amplification.RecoveryRowLeafTapes
import Proof.Hierarchy.CompetitorWitnessHeader
import Proof.Hierarchy.HierarchyBinaryMultiplyEntry

/-! The whole witness cap is checked before decoding. Each witness bit costs
sixteen input bits; an overlong witness is rejected without scanning its
unbounded suffix. These are literal steps of the fixed ordinary machine. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (q : Fin 34) (dx dw : HeadMove) (flag : Option Bool := none) : Action 3 34 :=
  ⟨q,![none,none,flag],![dx,dw,.stay]⟩
def machine : Machine 3 34 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==33
  rule := fun q cells=>
    if h0 : q.val=0 then
      some (if cells 1 then action 1 .stay .right else action 33 .stay .stay (some true))
    else if h1 : q.val≤16 then
      some (if cells 0 then action ⟨q.val+16,by omega⟩ .right .stay
        else action 33 .stay .stay (some false))
    else if h2 : q.val≤32 then
      some (if q.val=32 then action 0 .right .right
        else action ⟨q.val-15,by omega⟩ .right .stay)
    else none

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
