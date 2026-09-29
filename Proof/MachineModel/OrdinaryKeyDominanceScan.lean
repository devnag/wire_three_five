import Proof.MachineModel.OrdinaryCoordinateKey

/-! The keyed scan at the paper's literal dominance occurrence family. The
right/type selection and matrix padding are subsequent producer operations. -/
namespace NearCubicWires.RepairOrdinary.KeyLoop
open LocalBitMultitape SupplierPrinter SignedSortKey LeftPlaneCell
open KeyCell (config)
open RecordController (test)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def dominanceEntries {Rows Gates Columns : ℕ} (S K : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates) : List (ℤ × ℕ) :=
  (DominanceSort.sortedCopies S K leftScore rightScore gate).map
    (fun copy => (stableDominanceCopyScore leftScore rightScore gate copy, (stableDominanceCopyId copy).val))

theorem dominance_words {Rows Gates Columns : ℕ} (S K : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ K)
    (hlo : ∀ copy, -(2 ^ S : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ S : ℕ)) :
    words S K (dominanceEntries S K leftScore rightScore gate) =
      (DominanceLabels.request S K leftScore rightScore gate hsize).sortedWords := by
  rw [DominanceLabels.sorted_words S K leftScore rightScore gate hsize hlo hhi]
  simp only [words, dominanceEntries, List.map_map, dominanceRecord, Function.comp_def]

end NearCubicWires.RepairOrdinary.KeyLoop
