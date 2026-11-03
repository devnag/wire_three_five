import Proof.CaseAnalysis.RawRowsPaperMargin

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

theorem list_log_cap {α : Type} (xs : List α) (wires : α → ℕ) (logarithm : ℝ)
    (p : ℕ) (bound : ℝ) (hcap : ∀ c∈xs,(wires c : ℝ)*logarithm^p ≤ bound) :
    (((xs.map wires).sum : ℕ) : ℝ)*logarithm^p ≤ xs.length*bound := by
  induction xs with
  | nil => simp
  | cons c xs ih =>
    have hc := hcap c (by simp)
    have ht := ih (fun c hc => hcap c (by simp [hc]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hc,ht]

theorem wireScale_cap (q p : ℕ) (a : ℝ) (w : ℕ) (h : (w : ℝ) ≤ wireScale a p q) :
    (w : ℝ)*(logScale q : ℝ)^p ≤ a*(q : ℝ)^3 := by
  have hl : (0 : ℝ) < logScale q := by exact_mod_cast logScale_pos q
  exact (le_div_iff₀ (pow_pos hl p)).mp h

theorem symmetric_wire_cap (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (p : ℕ) (a : ℝ) (ha : 0 ≤ a) (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a p r.q) :
    (occurrenceWireCount (symmetricFourfoldOccurrences r) : ℝ)*(logScale r.q : ℝ)^p ≤
      4*a*(r.q : ℝ)^3 := by
  have hb := list_log_cap r.circuits (fun c => c.wireCount) (logScale r.q) p (a*(r.q : ℝ)^3)
    (fun c hc => wireScale_cap r.q p a c.wireCount (hcap c hc))
  have hw : (occurrenceWireCount (symmetricFourfoldOccurrences r) : ℝ) ≤
      (batchDescription NormalizedSymmetricThresholdCircuit.wireCount r.circuits : ℝ) := by
    exact_mod_cast symmetricFourfoldOccurrences_wireCount_le r
  have hfourR : (r.circuits.length : ℝ) ≤ 4 := by exact_mod_cast hfour
  calc
    _ ≤ (batchDescription NormalizedSymmetricThresholdCircuit.wireCount r.circuits : ℝ)*
        (logScale r.q : ℝ)^p := mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ r.circuits.length*(a*(r.q : ℝ)^3) := hb
    _ ≤ _ := by nlinarith [mul_nonneg ha (show 0 ≤ (r.q : ℝ)^3 by positivity)]

theorem threshold_wire_cap (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (p : ℕ) (a : ℝ) (ha : 0 ≤ a) (hfour : r.circuits.length ≤ 4)
    (hcap : ∀ c∈r.circuits,(c.wireCount : ℝ) ≤ wireScale a p r.q) :
    (occurrenceWireCount (thresholdFourfoldOccurrences r) : ℝ)*(logScale r.q : ℝ)^p ≤
      4*a*(r.q : ℝ)^3 := by
  have hb := list_log_cap r.circuits (fun c => c.wireCount) (logScale r.q) p (a*(r.q : ℝ)^3)
    (fun c hc => wireScale_cap r.q p a c.wireCount (hcap c hc))
  have hw : (occurrenceWireCount (thresholdFourfoldOccurrences r) : ℝ) ≤
      (batchDescription NormalizedThresholdThresholdCircuit.wireCount r.circuits : ℝ) := by
    exact_mod_cast thresholdFourfoldOccurrences_wireCount_le r
  have hfourR : (r.circuits.length : ℝ) ≤ 4 := by exact_mod_cast hfour
  calc
    _ ≤ (batchDescription NormalizedThresholdThresholdCircuit.wireCount r.circuits : ℝ)*
        (logScale r.q : ℝ)^p := mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ r.circuits.length*(a*(r.q : ℝ)^3) := hb
    _ ≤ _ := by nlinarith [mul_nonneg ha (show 0 ≤ (r.q : ℝ)^3 by positivity)]

end
end NearCubicWires.RepairSource.CloseoutRawRows
