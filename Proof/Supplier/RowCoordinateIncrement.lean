import Proof.Supplier.RowCoefficientWhole
import Proof.Circuits.MatrixBucketDimensionsIncrement

/-! Advance the coordinate template physically and retain its head-one ABI.
The existing unary increment allocates its new terminator and rewinds; the
two surrounding head moves are actual transitions with explicit cost. -/
namespace NearCubicWires.RepairOrdinary.RowCoordinateIncrement
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def shift (direction : HeadMove) : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun _=>direction⟩ else none
def first := Composition.machine (shift .left) MatrixBucketDimensions.Increment.machine
def machine := Composition.machine first (shift .right)


end NearCubicWires.RepairOrdinary.RowCoordinateIncrement
