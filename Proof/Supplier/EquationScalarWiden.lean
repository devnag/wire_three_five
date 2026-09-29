import Proof.Supplier.EquationRowRequest

/-! One actual streaming scalar widening for the B.2 doubled-cut producer.
It copies a framed field, appends one false high bit, consumes the original
terminator and retains the global destination append cursor. -/
namespace NearCubicWires.RepairOrdinary.EquationWiden
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==4
  rule := fun q bs =>
    if q.val=0 then some ⟨if bs 0 then 1 else 2,![none,some true],![.right,.right]⟩
    else if q.val=1 then some ⟨0,![none,some (bs 0)],![.right,.right]⟩
    else if q.val=2 then some ⟨3,![none,some false],![.stay,.right]⟩
    else if q.val=3 then some ⟨4,![none,some false],![.stay,.right]⟩
    else none

end NearCubicWires.RepairOrdinary.EquationWiden

