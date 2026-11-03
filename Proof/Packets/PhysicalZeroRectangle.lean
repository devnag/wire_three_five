import Proof.Packets.PhysicalZeroBank

/-! Allocate an entire positive walk transcript from an empty tape using
only the physical packet-width, column-count and transition-count drivers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroRectangle
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PhysicalZeroBank
noncomputable section

def backRow := Composition.machine MaskBack.machine MaskBack.machine

def appendRows := Composition.machine (RepeatMachine.machine PhysicalZeroBank.loop (fun _ _=>true))
  (TapeEmbedding.machine 1 PhysicalZeroBank.loop)
def backRows := Composition.machine (RepeatMachine.machine backRow (fun _ _=>true))
  (TapeEmbedding.machine 1 backRow)
def machine := Composition.machine appendRows backRows

attribute [local irreducible] PhysicalZeroBank.loop backRow

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroRectangle
