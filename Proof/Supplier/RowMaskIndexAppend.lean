import Proof.Supplier.RowTupleAdvance

/-! A selected monomial-mask bit appends the current positional index in
the exact internal occurrence format consumed by the common row bank. -/
namespace NearCubicWires.RepairOrdinary.RowMaskIndexAppend
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copy : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some (if bits 0 then
    ⟨0,![none,some true],![.right,.right]⟩ else ⟨1,![none,some false],![.stay,.right]⟩) else none

def last := TapeEmbedding.machine 1 UnaryTemplate.machine
def machine := Composition.machine copy last

end NearCubicWires.RepairOrdinary.RowMaskIndexAppend
