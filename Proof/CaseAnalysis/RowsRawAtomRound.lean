import Proof.Supplier.RowMaskBody
import Proof.MachineModel.Encoding

/-! One actual exact-child occurrence emits its absolute index in the
existing incidence stream. The original index copier/incrementer advances
the retained offset and count; only the two monomial delimiters are added. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRound
open LocalBitMultitape RecoveryExecution RowMaskBodyParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def mark (b : Bool) : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q=0 then some
    ⟨1,![none,none,some b,none],![.stay,.stay,.right,.stay]⟩ else none


end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRound
