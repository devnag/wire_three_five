import Proof.Amplification.RecoveryScratchErase
import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata
import Proof.Packets.UnaryAddCount

/-! The one-time terminal-to-delta literal-population change is an executed
copy, counted addition, cursor return, and scratch clear. Only master184
changes from population to twice population. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def pairUp := Composition.machine (PhysicalIndexReload.move (184 : Fin 299) .right)
  (PhysicalIndexReload.move (284 : Fin 299) .right)
def pairDown := Composition.machine (PhysicalIndexReload.move (284 : Fin 299) .left)
  (PhysicalIndexReload.move (184 : Fin 299) .left)
def addSlots : Fin 2→Fin 299 := ![184,284]
def addCounts := RecoveryFocus.machine addSlots UnaryAddCount.machine
def phaseDouble := Composition.machine (PhysicalCopyInto.machine (31 : Fin 299) 184 284)
  (Composition.machine pairUp (Composition.machine addCounts
    (Composition.machine pairDown (PhysicalCopyInto.machine (31 : Fin 299) 0 284))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
