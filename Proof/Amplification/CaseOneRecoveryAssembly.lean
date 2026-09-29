import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.Amplification.RecoveryWitnessPolicy
import Proof.Circuits.UnaryPolynomialSelector
import Proof.Foundations.CaseOneScheduleLedger
import Proof.MachineModel.ExecutableProgramRecoveryCompatibility

/-!
# Direct Case-1 recovery assembly

This module closes the STV branch against the exact smooth core schedules used
by the recovery language.  Source witnesses are selected only from
`PublishedContracts`; the remaining inputs are the canonical outer-PCP branch
data and its hierarchy-YES fact.  In particular, no semantic recovery callback
or separately chosen hard function crosses this boundary.
-/

namespace NearCubicWires.CaseOneRecoveryAssembly

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CaseOnePadding
open NearCubicWires.CaseOneScheduleLedger
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableProgramRecoveryCompatibility
open NearCubicWires.ExecutableProgramTimedSource
open NearCubicWires.ExecutableProgramTightRefuterSource
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PhysicalHardness
open NearCubicWires.PhysicalRecovery
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UnaryPolynomialSelector

/-- A sixteenth power absorbs either verified physical-circuit simulation. -/
def simulationPower : ℕ := 16

theorem wireScale_floor_le_cube
    {coefficient : ℝ} (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficientOne : coefficient ≤ 1)
    (logExponent arity : ℕ) :
    ⌊wireScale coefficient logExponent arity⌋₊ ≤ arity ^ 3 := by
  apply Nat.floor_le_of_le
  have hlogOne : (1 : ℝ) ≤ logScale arity := by
    exact_mod_cast (NearCubicWires.logScale_pos arity)
  have hdenominator :
      (1 : ℝ) ≤ (logScale arity : ℝ) ^ logExponent :=
    one_le_pow₀ hlogOne
  have hnPower : 0 ≤ (arity : ℝ) ^ 3 := by positivity
  calc
    wireScale coefficient logExponent arity =
        coefficient * (arity : ℝ) ^ 3 /
          (logScale arity : ℝ) ^ logExponent := rfl
    _ ≤ coefficient * (arity : ℝ) ^ 3 :=
      div_le_self (mul_nonneg hcoefficientNonnegative hnPower)
        hdenominator
    _ ≤ (arity : ℝ) ^ 3 :=
      mul_le_of_le_one_left hnPower hcoefficientOne
    _ = (arity ^ 3 : ℕ) := by norm_cast

/-- Uniform arithmetic ledger for the two DAG simulations.  The multiplier 50
dominates both concrete simulations, and arity six absorbs the constant. -/
theorem simulationCost_le_power
    (multiplier logExponent arity : ℕ)
    (hmultiplier : multiplier ≤ 50) (harity : 6 ≤ arity)
    {coefficient : ℝ} (hcoefficientNonnegative : 0 ≤ coefficient)
    (hcoefficientOne : coefficient ≤ 1) :
    multiplier *
        (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 ≤
      arity ^ simulationPower := by
  have hfloor :=
    wireScale_floor_le_cube hcoefficientNonnegative hcoefficientOne
      logExponent arity
  have hinside :
      arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2 ≤
        2 * arity ^ 3 := by
    have hcubic : arity + 2 ≤ arity ^ 3 := by
      calc
        arity + 2 ≤ arity + arity := by omega
        _ = arity * 2 := by ring
        _ ≤ arity * arity :=
          Nat.mul_le_mul_left arity (by omega)
        _ = arity ^ 2 := by ring
        _ ≤ arity ^ 2 * arity :=
          Nat.le_mul_of_pos_right _ (by omega)
        _ = arity ^ 3 := by ring
    omega
  have hpower :
      (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 ≤
        (2 * arity ^ 3) ^ 4 :=
    Nat.pow_le_pow_left hinside 4
  have hconstant : 800 ≤ arity ^ 4 := by
    have hsix : 6 ^ 4 ≤ arity ^ 4 :=
      Nat.pow_le_pow_left harity 4
    norm_num at hsix ⊢
    omega
  calc
    multiplier *
          (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 ≤
        50 *
          (arity + ⌊wireScale coefficient logExponent arity⌋₊ + 2) ^ 4 :=
      Nat.mul_le_mul hmultiplier le_rfl
    _ ≤ 50 * (2 * arity ^ 3) ^ 4 :=
      Nat.mul_le_mul_left 50 hpower
    _ = 800 * arity ^ 12 := by ring
    _ ≤ arity ^ 4 * arity ^ 12 :=
      Nat.mul_le_mul_right (arity ^ 12) hconstant
    _ = arity ^ simulationPower := by
      simp [simulationPower, ← pow_add]

/-! ### Frozen binary width of the actual scheduled factor geometry -/

/-! ### Cycle-free inverse compact-row constants -/

end NearCubicWires.CaseOneRecoveryAssembly
