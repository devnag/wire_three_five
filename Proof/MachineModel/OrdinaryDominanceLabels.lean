import Proof.MachineModel.OrdinarySortRank

/-! The combined ordinary sort/rank program at the exact B.3 occurrence
consumer. Its decoded rank is the existing canonical dominance rank. -/
namespace NearCubicWires.RepairOrdinary.SortRank
open LocalBitMultitape StablePartition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem carrier_budget (req : Request) :
    4 * (stream req.records).length + 3 + rawBudget req ≤
      512 * (req.records.length + 1) * (req.width + 1) ^ 2 := by
  have hw : SortPreparation.width req.records ≤ req.width := by
    cases he : req.records with
    | nil => simp [SortPreparation.width, SortPreparation.firstWord]
    | cons r rs =>
      have h := req.uniform r (by simp [he])
      simp only [SortPreparation.width, SortPreparation.firstWord, h, Nat.le_refl]
  have hs := SortCost.carrier_budget_le req.sortRequest
  have hmono := Nat.mul_le_mul_left (128 * (req.records.length + 1))
    (Nat.pow_le_pow_left (by omega : SortPreparation.width req.records + 1 ≤ req.width + 1) 2)
  change 4 * (stream req.records).length + 3 + SortCarrier.budget req.records ≤
    128 * (req.records.length + 1) * (SortPreparation.width req.records + 1) ^ 2 at hs
  have hsort := hs.trans hmono
  have hlinear : req.records.length * (7 * req.width + 14) + 4 ≤
      16 * (req.records.length + 1) * (req.width + 1) := by nlinarith
  have hsquare : req.width + 1 ≤ (req.width + 1) ^ 2 := by nlinarith
  have htail := hlinear.trans (Nat.mul_le_mul_left (16 * (req.records.length + 1)) hsquare)
  unfold rawBudget
  nlinarith [Nat.zero_le ((req.records.length + 1) * (req.width + 1) ^ 2)]

end NearCubicWires.RepairOrdinary.SortRank

namespace NearCubicWires.RepairOrdinary.DominanceLabels
open LocalBitMultitape StablePartition RadixSemantics SupplierPrinter SignedSortKey

def request {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits) : SortRank.Request where
  width := idBits + scoreBits + 1
  records := DominanceSort.records scoreBits idBits leftScore rightScore gate
  uniform := by
    intro r hr
    obtain ⟨copy, _, rfl⟩ := List.mem_map.mp hr
    exact encode_width scoreBits idBits _ _
  fits := by
    have hp : 0 < 2 ^ idBits := pow_pos (by decide) _
    have hq : 0 < 2 ^ scoreBits := pow_pos (by decide) _
    have hm := Nat.mul_le_mul_left (2 ^ idBits) (show 1 ≤ 2 ^ scoreBits by omega)
    simp only [DominanceSort.records, List.length_map, DominanceSort.copies, List.length_ofFn]
    rw [pow_succ, pow_add]
    nlinarith

theorem sorted_words {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ)) :
    (request scoreBits idBits leftScore rightScore gate hsize).sortedWords =
      (DominanceSort.sortedCopies scoreBits idBits leftScore rightScore gate).map
        (fun copy => word (dominanceRecord scoreBits idBits leftScore rightScore gate copy)) := by
  change (SortCarrier.sorted (DominanceSort.request scoreBits idBits leftScore rightScore gate)).map word = _
  have h := congrArg (List.map word)
    (DominanceSort.sorted_output scoreBits idBits leftScore rightScore gate hsize hlo hhi)
  simpa only [List.map_map, Function.comp_def] using h.symm

end NearCubicWires.RepairOrdinary.DominanceLabels
