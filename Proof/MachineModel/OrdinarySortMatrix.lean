import Proof.MachineModel.OrdinaryLeftMatrix

/-! Actual coordinate sort, paid reset, and selected padded-matrix traversal.
Dimension templates are supplied explicitly and preserved across the sorter. -/
namespace NearCubicWires.RepairOrdinary.SortMatrix
open LocalBitMultitape SupplierPrinter CoordinateKey GridRows LeftPlaneCell
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def sortMachine : Machine 11 88 := TapeEmbedding.machine 4 (Rewind.machine SortCarrier.machine)

theorem final_cells {t s space n : ℕ} {p : Machine t s} {c d : Configuration t s}
    (hp : Prefix p space n c d) : d.tapeCells ≤ space := by
  induction hp with
  | refl c hc => exact hc
  | step _ _ _ _ ih => exact ih

theorem sorted_stream_length (req : SortCarrier.Request) :
    (StablePartition.stream (SortCarrier.sorted req)).length = (StablePartition.stream req.records).length := by
  have hw : ∀ r ∈ SortCarrier.sorted req, (RadixSemantics.word r).length = SortPreparation.width req.records :=
    fun r hr => req.uniform r ((SortCarrier.sorted_perm req).mem_iff.mp hr)
  rw [SortCost.stream_length_of_width _ _ hw, SortCost.stream_length_of_width _ _ req.uniform,
    (SortCarrier.sorted_perm req).length_eq]

end NearCubicWires.RepairOrdinary.SortMatrix
