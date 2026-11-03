import Proof.SourceAssembly.SourceClearBound
import Proof.MachineModel.RuntimeShapeClasses
import Proof.CaseAnalysis.CapacityPower
import Proof.SourceAssembly.SourceLiveCount

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.SupplierEstimator
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
namespace NearCubicWires.SourceConstruction

/-! ## 1. The capacity -/

theorem one_le_tableClass (L h q : ℕ) : 1 ≤ tableClass L h q :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity))

/-! ## 2. Forced: `R` is table class, and the window cannot contain an `R`-sized stage -/

/-! ## 3. Sufficient: `CallBound` from a table-class window -/

/-! ## 4. What `R` costs, by class -/

theorem power_class (L q : ℕ) :
    RepairSource.CloseoutCapacity.Power.budget (q - normalizedLiveCount q L) ≤
      300 * tableClass L 1 q := by
  set d := q - normalizedLiveCount q L with hd
  have hdq : d ≤ q := by omega
  change RepairSource.CloseoutCapacity.Power.budget d ≤ 300 * ((q+1)^1 * 2^d)
  rw [pow_one]
  simp only [RepairSource.CloseoutCapacity.Power.budget, MatrixScorePower.budget,
    MatrixUnaryTemplate.budget]
  have hP : 1 ≤ 2^d := Nat.one_le_two_pow
  have h1 : d * 2^d ≤ (q+1) * 2^d := Nat.mul_le_mul_right _ (by omega)
  have h2 : 2^d ≤ (q+1) * 2^d := Nat.le_mul_of_pos_left _ (by omega)
  have h3 : d ≤ (q+1) * 2^d := le_trans (by omega : d ≤ q+1) (Nat.le_mul_of_pos_right _ hP)
  ring_nf
  ring_nf at h1 h2 h3
  omega

theorem logScale_le (q : ℕ) : logScale q ≤ q+1 := by
  unfold logScale
  apply Nat.clog_le_of_le_pow
  have := @Nat.lt_two_pow_self (q+1)
  omega

/-! ## 5. Where the dimension comes from -/

end NearCubicWires.SourceConstruction
end
