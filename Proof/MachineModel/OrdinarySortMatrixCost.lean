import Proof.MachineModel.OrdinarySortMatrix

/-! Dimension and bit-width costs at the actual sorted-grid matrix consumer. -/
namespace NearCubicWires.RepairOrdinary.SortMatrix
open LocalBitMultitape SupplierPrinter CoordinateKey GridRows LeftPlaneCell
open StablePartition (Record recordsBits)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem width_le {Rows Columns Used : ℕ} (I K : ℕ)
    (payload : Fin (Rows + Columns) → Fin Used → Bool) (req : SortCarrier.Request)
    (hgrid : SortCarrier.sorted req = grid I K payload) : SortPreparation.width req.records ≤ I + K + 1 := by
  have hw : ∀ r ∈ req.records, (RadixSemantics.word r).length = I + K + 1 := by
    intro r hr
    have hm := (SortCarrier.sorted_perm req).mem_iff.mpr hr
    rw [hgrid] at hm
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hm
    exact key_width _ _ _ _ _
  cases he : req.records with
  | nil => simp [SortPreparation.width, SortPreparation.firstWord]
  | cons r rs =>
    have h := hw r (by simp [he])
    simp only [SortPreparation.width, SortPreparation.firstWord, h, Nat.le_refl]

end NearCubicWires.RepairOrdinary.SortMatrix
