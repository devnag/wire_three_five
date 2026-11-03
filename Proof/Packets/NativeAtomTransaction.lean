import Proof.Packets.NativeAtomClear

/-! One closed reusable dense-atom transaction: copy the resident raw atom
pair, parse and normalize it, read its actual singleton code, overwrite the
selected dense entry, and reset operand/index work for the next atom. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair word)

def answer (C : Nat) (p : Pair) := NormalizerOrder.ordered (NativeNormalized.masks C (p.1++p.2))
noncomputable def transaction := Composition.machine (TapeEmbedding.machine 4 NativePairNormalize.machine)
  (Composition.machine parse (Composition.machine store cleanup))

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
