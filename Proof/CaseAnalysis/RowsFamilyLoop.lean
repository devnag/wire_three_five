import Proof.CaseAnalysis.RowsBankPacket

/-! The actual outer family loop consumes every polynomial packet once,
including empty polynomials, and rewinds its literal family driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsFamilyLoop
open LocalBitMultitape CloseoutRowsBankPacket CloseoutRowsPreparationBounds
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flatMap_index {α β : Type} (xs : List α) (default : α) (f : α→List β) :
    (List.range xs.length).flatMap (fun j=>f (xs.getD j default))=xs.flatMap f := by
  have he : (List.range xs.length).map (fun j=>xs.getD j default)=xs := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp only [List.getElem_map,List.getElem_range]
      exact List.getD_eq_getElem xs default hi
  rw [←List.flatMap_map,he]

theorem split_word {α β : Type} (xs : List α) (default : α) (f : α→List β)
    (j : ℕ) (hj : j<xs.length) :
    xs.flatMap f=(xs.take j).flatMap f++f (xs.getD j default)++(xs.drop (j+1)).flatMap f := by
  have h:=congrArg (List.flatMap f) (List.take_append_drop (j+1) xs)
  rw [List.take_succ_eq_append_getElem hj] at h
  simpa only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.getD_eq_getElem xs default hj] using h.symm

theorem next_word {α β : Type} (xs : List α) (default : α) (f : α→List β)
    (j : ℕ) (hj : j<xs.length) :
    ((xs.take (j+1)).flatMap f).length=
      ((xs.take j).flatMap f).length+(f (xs.getD j default)).length := by
  simp only [List.take_succ_eq_append_getElem hj,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.length_append,List.getD_eq_getElem xs default hj]


end NearCubicWires.RepairOrdinary.CloseoutRowsFamilyLoop
