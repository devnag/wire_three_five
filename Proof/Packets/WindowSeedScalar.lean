import Proof.Packets.WindowSeedPrimitives

/-! Actual M-1 and framed scalar construction for the subset enumerator.
Both retained metadata counters return to head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def countPred := Composition.machine (Completion.PhysicalDriverMoves.machine 1 .right)
  (Composition.machine VectorCounter.decrement (Completion.PhysicalDriverMoves.machine 1 .left))

def countSlot : Fin 1→Fin 3 := ![2]
def valueUp := RecoveryFocus.machine countSlot (Completion.PhysicalDriverMoves.machine 1 .right)
def valueDown := RecoveryFocus.machine countSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def scalarValue := Composition.machine valueUp (Composition.machine ScalarFromCounter.machine valueDown)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
