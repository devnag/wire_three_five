import Proof.CaseAnalysis.RawRowsMonomials
import Proof.CaseAnalysis.RowsRawLogShape

/-! The actual SYM/THR raw degrees and count budgets fit the checked paper
load expression. The population/child logarithm is kept explicit. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator
open SupplierListPolynomial SupplierListSchedule SupplierWalkBridge SupplierTouching
open RepairRepresentation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section


theorem rawDegree_window_sum {depth : ℕ} (window : Fin depth → ℕ) :
    structuralListCoordinateRawDegree depth window gradedTerminalWindow = 2*∑ i,window i := by
  rw [structuralListCoordinateRawDegree_eq_listDegree,listDegree_eq_terminal_add_sum]
  simp only [gradedTerminalWindow,Nat.zero_add,Finset.mul_sum]

end
end NearCubicWires.RepairSource.CloseoutRawRows
