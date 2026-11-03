import Proof.Packets.DescendingWindowCounters
import Proof.CaseAnalysis.RowsMetadataCopy
import Proof.Amplification.RecoveryScratchErase
import Proof.MachineModel.OrdinaryTransitionTapeZero

/-! The descending window's real per-degree setup: erase its old unary
coordinate, copy the retained degree, zero the framed complement, and
advance the retained inner count. Every local cursor returns to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowPrepare
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.SignedSortKey

def clearSlots : Fin 3→Fin 5 := ![0,3,4]
def copySlots : Fin 4→Fin 5 := ![2,0,3,4]
def zeroSlots : Fin 2→Fin 5 := ![1,4]
def advanceSlots : Fin 1→Fin 5 := ![2]
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def copy := RecoveryFocus.machine copySlots RecoveryBoundedTapeCopy.machine
noncomputable def zero := RecoveryFocus.machine zeroSlots TransitionTapeZero.machine
noncomputable def increment := Composition.machine
  (Composition.machine (Completion.PhysicalDriverMoves.machine 1 .right) VectorCounter.increment)
  (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def advance := RecoveryFocus.machine advanceSlots increment
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine clear copy) zero) advance

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowPrepare
