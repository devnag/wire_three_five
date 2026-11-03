import Proof.CaseAnalysis.RowsTupleSeekPairs
import Proof.MachineModel.OrdinaryMatrixNaturalHeader
import Proof.PCP.PCPPQueryField
import Proof.PCP.PCPPQueryNatural

/-! Retain the already-read bottom count in the mask consumer's unary
stream. The count driver's false terminator is copied even when n is zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countMachine (keep : Bool) : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q=0 then
    some ⟨if bits 0 then 0 else 1,![none,if keep then some (bits 0) else none],
      ![.right,if keep then .right else .stay]⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
