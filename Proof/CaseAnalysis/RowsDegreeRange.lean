import Proof.CaseAnalysis.RowsCutMeaning

/-! The physical degree loop may use its existing Q driver. Degrees above
the actual monomial count emit no positional subset, so no extra physical
min(Q,M) controller is needed and the exact cut list is unchanged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeRange
open MatrixScoreBatch CloseoutRowsCutMeaning CloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_nil (w M j : ℕ) (hw : M≤2^w) (hj : M≤j) :
    RowTupleSubsets.selected w M (j+1)=[] := by
  have h := RowTupleSubsets.selected_perm w M (j+1) hw
  have hb : (List.range M).length<j+1 := by simp; omega
  rw [List.sublistsLen_of_length_lt hb] at h
  exact List.perm_nil.mp h

theorem degree_nil {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (w j : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) (hj : rows.length≤j) :
    degreeCuts gs w j rows=[] := by
  simp only [degreeCuts,selected_nil w rows.length j hw hj,List.map_nil]

theorem all_degrees {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (Q w : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (List.range Q).flatMap (fun j=>degreeCuts gs w j rows)=
      (List.range (min Q rows.length)).flatMap (fun j=>degreeCuts gs w j rows) := by
  by_cases hQ : Q≤rows.length
  · rw [Nat.min_eq_left hQ]
  · have hM : rows.length≤Q := by omega
    rw [Nat.min_eq_right hM]
    clear hQ
    induction Q,hM using Nat.le_induction with
    | base => rfl
    | succ Q hQ ih =>
      simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,degree_nil gs w Q rows hw hQ,ih]

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeRange
