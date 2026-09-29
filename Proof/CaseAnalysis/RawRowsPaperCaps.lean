import Proof.CaseAnalysis.RawRowsLoad

/-! Per-circuit paper wire caps feed the same actual occurrence pool and
TouchingSelect. Powers5/9 give the squared-load powers4/8 exactly. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierTouching
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem wireScale_cap (q p : ℕ) (a : ℝ) (w : ℕ) (h : (w : ℝ) ≤ wireScale a p q) :
    (w : ℝ)*(logScale q : ℝ)^p ≤ a*(q : ℝ)^3 := by
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  exact (le_div_iff₀ (pow_pos hl p)).mp h

end
end NearCubicWires.RepairSource.CloseoutRawRows
