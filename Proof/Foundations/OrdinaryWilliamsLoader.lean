import Proof.Foundations.OrdinaryStreaming
import Proof.Foundations.OperationalWilliamsSourceCore

/-!
The paid copy-and-rewind applied to the real corrected Williams input format.
This consumes a generated framed stream. Constructing that stream from the
row generator, and linking the published multiplication machine, remain
separate producer/composition obligations; neither is hidden in this receipt.
-/
namespace NearCubicWires.RepairOrdinary.WilliamsLoader
open LocalBitMultitape SourceInterfaces WilliamsLoaderForms
open WilliamsPublishedForm
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem matrix_length {r c : ℕ} (a : BitMatrix r c) :
    (rowMajorBitMatrix a).length = r * c := by
  simp [rowMajorBitMatrix, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.ofFn_const]

@[simp] theorem nat_frame_length (u : ℕ) :
    (framedNatBits u).length = 2 * natBitLength u + 1 := by
  simp [framedNatBits, WilliamsPublishedForm.fixedWidthNatBits]
  omega

end NearCubicWires.RepairOrdinary.WilliamsLoader
