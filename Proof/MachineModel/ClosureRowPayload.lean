import Proof.MachineModel.ClosureActualRow

/-! The immediate raw-family consumer requires binary counts, whereas the
checked row printer emits six framed fields. Reuse the existing field skipper
and unframer: five skips, then one copy. The machine depends on no runtime row,
width, coefficient or answer. This is paid per-row input/output processing in
the A.13.9/A.13.10 supplier charge. Source positioning remains explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RowPayload
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open CloseoutRowsEstimatorCoefficients CompetitorRationalDecision SignedSortKey

private def states : Nat → Nat
  | 0 => 3
  | k+1 => 3+states k
private def reader : (k : Nat) → Machine 2 (states k)
  | 0 => GeneratedAmplifier.Copy.machine
  | k+1 => Composition.machine (TapeEmbedding.machine 1 MatrixScoreSkipField.machine) (reader k)

def machine := reader 5
def budget (b : Nat) := 20*b+27

end NearCubicWires.P1Closure.RowPayload
