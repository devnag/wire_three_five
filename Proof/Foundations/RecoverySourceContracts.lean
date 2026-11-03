import Proof.Foundations.SourceCore
import Proof.Foundations.CaseOneScheduleLedger
import Proof.Foundations.PhysicalRecovery
import Statement

/-!
Source-faithful Case-1 amplification for one cutoff schedule at a time.
The absolute STV exponent precedes the cutoff degree. The ordinary constructor,
its arity constant and its exponential clock are selected afterwards. Its
literal input and output are framed dimensions followed by complete truth
 tables. Neither a universal later-cutoff claim nor an arity-only polynomial
 table evaluator occurs at this source boundary.

CLW3.9/STV supply the truth-table algorithm. Polynomial ordinary-machine and
framing conversions are absorbed in the selected exponential clock; concrete
format/load/copy implementations and generated-table lookup remain local.
-/
namespace NearCubicWires.RepairSource
open ExecutableInterfaces SourceInterfaces RecoveryPipeline OuterPCPRecovery
open RecoveryScheduleEnvelope PolynomialClock CaseOneScheduleLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


/-- The output depends on the cutoff d selected before the constructor. -/
structure ScheduleAmplifier (stvExponent requiredDegree : ℕ) where
  arityCoefficient : ℕ
  arityCoefficientPositive : 1 ≤ arityCoefficient
  output : (q : ℕ) → BoolFunction q → AmplifierOutput
  arityBound : ∀ q f, 1 ≤ q → (output q f).arity ≤ arityCoefficient * q
  sound : ∀ q f, 1 ≤ q →
    WorstCaseHardAt f (oracleSizeBound requiredDegree q) →
    ∀ circuit : BooleanCircuit (output q f).arity,
      circuit.size ≤ integerFloorRoot stvExponent (oracleSizeBound requiredDegree q) →
      agreement circuit.eval (output q f).function ≤
        1 / 2 + Real.rpow (oracleSizeBound requiredDegree q : ℝ)
          (-(1 : ℝ) / stvExponent)


def amplifierOutput {c d : ℕ} (amplifier : ScheduleAmplifier c d)
    (request : AmplifierRequest) : List Bool :=
  RepairOrdinary.frame (amplifier.output request.inputArity request.function).arity.bits ++
    boolFunctionTable (amplifier.output request.inputArity request.function).function

structure OrdinaryScheduleAmplifier (c d : ℕ) extends ScheduleAmplifier c d where
  constructionExponent : ℕ
  constructionExponentPositive : 1 ≤ constructionExponent
  constructor : OrdinaryWordFunction AmplifierRequest amplifierInput
    (amplifierOutput toScheduleAmplifier)
    (fun request => 2 ^ (constructionExponent * max 1 request.inputArity))

/-- One source constituent. The algorithm promised by the source is retained;
there is no semantic-only witness with algorithm existence delegated locally. -/
structure SourceAmplifierFactory where
  stvExponent : ℕ
  stvExponentPositive : 1 ≤ stvExponent
  forSchedule : ∀ requiredDegree,
    Nonempty (OrdinaryScheduleAmplifier stvExponent requiredDegree)

/-- Existing Case-1 size currency, independent of any executable amplifier. -/
theorem amplifier_size_ge_power (c d power q : ℕ) (hc : 0 < c)
    (hq : 0 < q) (hdegree : power * c ≤ d) :
    q ^ power ≤ integerFloorRoot c (oracleSizeBound d q) := by
  apply pow_le_integerFloorRoot_of_mul_le hc hq
  · exact hdegree.trans (requiredDegree_le_oracleDegree d)
  · exact pow_twoPow_le_pairClock (oracleDepth d) q

theorem amplifier_advantage_le_power (c d power q : ℕ) (hc : 0 < c)
    (hq : 0 < q) (hdegree : power * c ≤ d) :
    Real.rpow (oracleSizeBound d q : ℝ) (-(1 : ℝ) / c) ≤
      inversePolynomialAdvantage q (power : ℝ) := by
  have hpowerNat : q ^ (power * c) ≤ oracleSizeBound d q :=
    (Nat.pow_le_pow_right hq
      (hdegree.trans (requiredDegree_le_oracleDegree d))).trans
        (pow_twoPow_le_pairClock (oracleDepth d) q)
  have hpowerReal : (q : ℝ) ^ (power * c) ≤ (oracleSizeBound d q : ℝ) := by
    exact_mod_cast hpowerNat
  have hn : -(1 : ℝ) / c ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  calc
    _ ≤ Real.rpow ((q : ℝ) ^ (power * c)) (-(1 : ℝ) / c) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hpowerReal hn
    _ = Real.rpow (q : ℝ) (-(power : ℝ)) := by
      rw [← Real.rpow_natCast]
      push_cast
      calc
        Real.rpow (Real.rpow (q : ℝ) ((power : ℝ) * (c : ℝ))) (-(1 : ℝ) / c) =
            Real.rpow (q : ℝ) (((power : ℝ) * (c : ℝ)) * (-(1 : ℝ) / c)) :=
          (Real.rpow_mul (x := (q : ℝ)) (by positivity)
            ((power : ℝ) * (c : ℝ)) (-(1 : ℝ) / c)).symm
        _ = Real.rpow (q : ℝ) (-(power : ℝ)) := by
          congr 1
          field_simp
    _ = _ := rfl

end NearCubicWires.RepairSource
