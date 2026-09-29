import Proof.MachineModel.OrdinarySignedSortKey

/-! The actual sorting carrier applied to the existing paper B.3 occurrence
keys. Decoding its literal output gives the signed-score/stable-id order used
by the existing rank and bucket mathematics. -/
namespace NearCubicWires.RepairOrdinary.DominanceSort
open LocalBitMultitape StablePartition RadixSemantics SupplierPrinter SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def copies (Rows Columns : ℕ) : List (StableDominanceCopy Rows Columns) :=
  List.ofFn finSumFinEquiv.symm

def records {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates) :
    List Record := (copies Rows Columns).map (dominanceRecord scoreBits idBits leftScore rightScore gate)

def fixedRequest (rs : List Record) (bits : ℕ) (hw : ∀ r ∈ rs, (word r).length = bits) :
    SortCarrier.Request where
  records := rs
  uniform := by
    cases rs with
    | nil => simp
    | cons r rs =>
      intro a ha
      have hfirst := hw r (by simp)
      have ha' := hw a ha
      simpa only [SortPreparation.width, SortPreparation.firstWord, hfirst] using ha'

def request {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates) :
    SortCarrier.Request :=
  fixedRequest (records scoreBits idBits leftScore rightScore gate) (idBits + scoreBits + 1) (by
    intro r hr
    obtain ⟨copy, _, rfl⟩ := List.mem_map.mp hr
    exact encode_width scoreBits idBits _ _)

def decodeCopy (Rows Columns idBits : ℕ) (r : Record) : Option (StableDominanceCopy Rows Columns) :=
  if h : decodeId idBits r < Rows + Columns then some (finSumFinEquiv.symm ⟨decodeId idBits r, h⟩)
  else none

theorem decode_record {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ))
    (copy : StableDominanceCopy Rows Columns) :
    decodeCopy Rows Columns idBits (dominanceRecord scoreBits idBits leftScore rightScore gate copy) =
      some copy := by
  unfold decodeCopy dominanceRecord
  rw [decode_id _ _ _ _ (hlo copy) (hhi copy) ((stableDominanceCopyId copy).isLt.trans_le hsize)]
  simp only [(stableDominanceCopyId copy).isLt, ↓reduceDIte]
  exact congrArg some (finSumFinEquiv.symm_apply_apply copy)

noncomputable def sortedCopies {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates) :
    List (StableDominanceCopy Rows Columns) :=
  (SortCarrier.sorted (request scoreBits idBits leftScore rightScore gate)).filterMap
    (decodeCopy Rows Columns idBits)

theorem sorted_output {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ)) :
    (sortedCopies scoreBits idBits leftScore rightScore gate).map
        (dominanceRecord scoreBits idBits leftScore rightScore gate) =
      SortCarrier.sorted (request scoreBits idBits leftScore rightScore gate) := by
  let req := request scoreBits idBits leftScore rightScore gate
  have hp := SortCarrier.sorted_perm req
  rw [sortedCopies, List.map_filterMap]
  calc
    _ = (SortCarrier.sorted req).filterMap some := by
      apply List.filterMap_congr
      intro r hr
      obtain ⟨copy, _, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp hr)
      rw [decode_record _ _ _ _ _ hsize hlo hhi]
      rfl
    _ = _ := List.filterMap_some

theorem sorted_semantics {Rows Gates Columns : ℕ} (scoreBits idBits : ℕ)
    (leftScore : IntMatrix Rows Gates) (rightScore : IntMatrix Gates Columns) (gate : Fin Gates)
    (hsize : Rows + Columns ≤ 2 ^ idBits)
    (hlo : ∀ copy, -(2 ^ scoreBits : ℕ) ≤ stableDominanceCopyScore leftScore rightScore gate copy)
    (hhi : ∀ copy, stableDominanceCopyScore leftScore rightScore gate copy < (2 ^ scoreBits : ℕ)) :
    (sortedCopies scoreBits idBits leftScore rightScore gate).Perm (copies Rows Columns) ∧
      (sortedCopies scoreBits idBits leftScore rightScore gate).Pairwise
        (fun a b => stableDominanceKey leftScore rightScore gate a ≤ stableDominanceKey leftScore rightScore gate b) := by
  let req := request scoreBits idBits leftScore rightScore gate
  have hp := (SortCarrier.sorted_perm req).filterMap (decodeCopy Rows Columns idBits)
  have hin : req.records.filterMap (decodeCopy Rows Columns idBits) = copies Rows Columns := by
    change ((copies Rows Columns).map _).filterMap _ = _
    rw [List.filterMap_map]
    have he : (decodeCopy Rows Columns idBits ∘ dominanceRecord scoreBits idBits leftScore rightScore gate) = some := by
      funext copy
      exact decode_record scoreBits idBits leftScore rightScore gate hsize hlo hhi copy
    rw [he, List.filterMap_some]
  refine ⟨?_, ?_⟩
  · rw [hin] at hp
    exact hp
  have hs := SortCarrier.sorted_order req
  rw [← sorted_output scoreBits idBits leftScore rightScore gate hsize hlo hhi, List.pairwise_map] at hs
  exact hs.imp (fun {a b} hab => (dominance_order scoreBits idBits leftScore rightScore gate hsize hlo hhi a b).mp hab)

end NearCubicWires.RepairOrdinary.DominanceSort
