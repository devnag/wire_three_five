import Proof.CaseAnalysis.RawRowsModeBounds
import Proof.CaseAnalysis.RawRowsThresholdAccuracy
import Proof.CaseAnalysis.RawRowsThresholdSize
import Mathlib.Algebra.Order.Floor.Semifield

/-! The physical mode guard uses natural division, with one fixed positive
integer denominator. Its accepted cap is exactly the real wireScale floor;
the paper margin permits this choice without computing any real constant. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open SupplierPipeline SupplierEstimator SupplierWalkBridge SupplierTouching SupplierPrime
open SourceInterfaces RepairRepresentation PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def naturalWireCap (den exponent q : Nat) := q^3 / (den * logScale q^exponent)

theorem naturalWireCap_floor (den exponent q : Nat) :
    ⌊wireScale (1 / (den : ℝ)) exponent q⌋₊ = naturalWireCap den exponent q := by
  have he : wireScale (1 / (den : ℝ)) exponent q =
      ((q^3 : Nat) : ℝ) / ((den * logScale q^exponent : Nat) : ℝ) := by
    simp only [wireScale, Nat.cast_pow, Nat.cast_mul, div_eq_mul_inv,
      one_mul, mul_inv_rev]
    ring
  rw [he, Nat.floor_div_eq_div]
  rfl

end
end NearCubicWires.RepairSource.CloseoutRawRows
