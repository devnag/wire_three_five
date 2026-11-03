import Proof.Packets.ScalarFromCounter
import Proof.Rows.PhysicalFocusBoundary
import Proof.PCP.VerifierDecodingUnaryFrame

/-! Runtime scalar width physically allocates a zero binary frame. The width
counter and rewind reserve are retained; the output begins as blank capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarCounterSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots : Fin 2→Fin 3 := ![1,2]
def machine := Composition.machine (TapeEmbedding.machine 1 UnaryFrameMachine.machine)
  (RecoveryFocus.machine slots TransitionTapeZero.machine)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarCounterSeed
