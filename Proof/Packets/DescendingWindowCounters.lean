import Proof.Packets.VectorCounterDecrement
import Proof.MachineModel.OrdinaryFramedIncrement
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.PhysicalFocusBoundary

/-! Actual descending inner-window coordinates: decrement the unary
elementary degree and increment its framed binary complement. Both counters
and the retained physical log return to head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowCounters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.SignedSortKey

noncomputable def unary := Composition.machine
  (Composition.machine (Completion.PhysicalDriverMoves.machine 1 .right) VectorCounter.decrement)
  (Completion.PhysicalDriverMoves.machine 1 .left)

def unarySlots : Fin 1→Fin 3 := ![0]
def binarySlots : Fin 2→Fin 3 := ![1,2]
noncomputable def unaryPart := RecoveryFocus.machine unarySlots unary
noncomputable def binaryPart := RecoveryFocus.machine binarySlots FramedIncrement.machine
noncomputable def machine := Composition.machine unaryPart binaryPart

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowCounters
