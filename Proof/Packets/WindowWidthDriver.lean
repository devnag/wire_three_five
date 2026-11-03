import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.VectorCounter

/-! The resident half-window W physically supplies the 2W+1 outer driver:
two actual W-counted increment loops and one final increment. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowWidthDriver
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def count := RepeatMachine.machine VectorCounter.increment (fun _ _=>true)
def increment := TapeEmbedding.machine 1 VectorCounter.increment
def up := Completion.PhysicalDriverMoves.machine 2 .right
def down := Completion.PhysicalDriverMoves.machine 2 .left
def machine := Composition.machine up (Composition.machine count
  (Composition.machine count (Composition.machine increment down)))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowWidthDriver
