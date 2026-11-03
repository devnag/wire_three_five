import Proof.CaseAnalysis.RowsOriginalPairClean
import Proof.CaseAnalysis.RowsTupleSeekCount
import Proof.MachineModel.Encoding

/-! One retained original proof-coordinate emits its unary factor index.
The paid return keeps the index available for repeated template factors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBlock
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsTupleSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (bit : Bool) : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q=0 then some ⟨1,![none,some bit],![.stay,.right]⟩ else none

def raw:=Composition.machine (mark true) (countMachine true)
def machine:=MaskedReset.machine raw (fun i=>decide (i=0))

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBlock
