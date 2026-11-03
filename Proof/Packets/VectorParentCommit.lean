import Proof.Packets.VectorChildTransaction
import Proof.Packets.VectorAccumulatorReset
import Proof.Packets.PacketBankWrite

/-! The actual parent epilogue writes the completed accumulator into the next
resident vector at its physical parent index, then erases saved accumulator
storage by copying the retained zero tape. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorParentCommit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots : Fin 6→Fin 41 := ![31,39,37,38,40,36]
def store := RecoveryFocus.machine slots PacketBank.storeSelectedZero
def reset := TapeEmbedding.machine 2 (RecoveryFocus.machine VectorChildTransaction.slots VectorAccumulator.reset)
def machine := Composition.machine store reset

attribute [local irreducible] PacketBank.storeSelectedZero PacketBank.storeSelected

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorParentCommit
