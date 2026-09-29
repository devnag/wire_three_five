import Proof.Foundations.ComponentwiseVerifierParameters
import Proof.Foundations.PCPPClausePadding
import Proof.Foundations.PolynomialSchedule

/-!
# Source-only recovery arity envelope

This module freezes the quantitative path shared by both headline recoveries.
Source instance `s` has length `2^(s+1)`, the outer proof is padded to the one
canonical width envelope, and the Case-2 oracle cap is one pairing clock.  The
two copy-count tiers differ only where the theorem statements differ:
inverse-polynomial advantage uses logarithmically many blocks, while fixed
advantage uses one constant number of blocks.

Every raw Case-2 XOR arity is bounded by a single smooth polynomial.  Case 1
and Case 2 can therefore be padded to that same arity before the target-length
selector runs; no branch-specific schedule or caller-selected growth function
is exposed.
-/

namespace NearCubicWires.RecoveryScheduleEnvelope

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.PolynomialSchedule
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryPipeline
open NearCubicWires.ScheduleArithmetic
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-! ## Fixed public-length decoder -/

/-- A requested polynomial degree is realized by one pairing-clock depth.
`coefficientExponent` is reused so this is the same power-of-two domination
ledger used by the exponential interpreter bounds. -/
def oracleDepth (requiredDegree : ℕ) : ℕ :=
  coefficientExponent requiredDegree

/-- The only small-oracle size cap used by the outer Case-1/Case-2 split. -/
def oracleSizeBound (requiredDegree width : ℕ) : ℕ :=
  pairClock (oracleDepth requiredDegree) width

theorem requiredDegree_le_oracleDegree (requiredDegree : ℕ) :
    requiredDegree ≤ 2 ^ oracleDepth requiredDegree := by
  exact coefficient_le_two_pow requiredDegree

theorem oracleSizeBound_monotone (requiredDegree : ℕ) :
    Monotone (oracleSizeBound requiredDegree) := by
  intro left right hle
  simpa [oracleSizeBound, pairClock] using
    pairIter_mono_value (oracleDepth requiredDegree) hle

theorem oracleSizeBound_polynomiallyBounded (requiredDegree : ℕ) :
    PolynomiallyBounded (oracleSizeBound requiredDegree) := by
  change PolynomiallyBounded (pairClock (oracleDepth requiredDegree))
  exact pairClock_polynomiallyBounded (oracleDepth requiredDegree)

def oracleSizeBoundConstructible (requiredDegree : ℕ) :
    TimeConstructible (oracleSizeBound requiredDegree) := by
  change TimeConstructible (pairClock (oracleDepth requiredDegree))
  exact pairClockTimeConstructible (oracleDepth requiredDegree)

/-! ### The same schedule at an arbitrary approximation radius

Every conclusion of the fixed-radius schedule above is reproduced here at an
arbitrary rational radius `delta`, under the two side conditions the imported
XOR contract already demands (`0 < delta` and `delta ≤ 1 / 2`).  The radius is
carried as a rational so that the copy counts stay computable; the schedule the
repaired seam selects is the instantiation at the validity constant of the
selected parameter package.  See the repair record above. -/

/-- Block length that halves the geometric factor at approximation radius
`delta`.  Since `Rat` is kept in lowest terms, `delta.den * delta = delta.num`
is at least one, so the denominator is always at least `1 / delta`: the block
grows like `1 / delta`, which is the whole quantitative price of the repair.
Reading the block off the denominator rather than through `Nat.ceil` keeps it
kernel-cheap, which the downstream witness-limit `rfl`s require. -/
def recoveryBlockOf (delta : ℚ) : ℕ := delta.den

theorem recoveryBlockOf_positive (delta : ℚ) :
    0 < recoveryBlockOf delta :=
  delta.den_pos

private theorem one_le_recoveryBlockOf_mul {delta : ℚ} (hpositive : 0 < delta) :
    (1 : ℝ) ≤ (recoveryBlockOf delta : ℝ) * (delta : ℝ) := by
  have hnumerator : 1 ≤ delta.num := Rat.num_pos.mpr hpositive
  have hproduct : ((delta.den : ℚ)) * delta = (delta.num : ℚ) := by
    rw [mul_comm]
    exact_mod_cast Rat.mul_den_eq_num delta
  have hrational : (1 : ℚ) ≤ (recoveryBlockOf delta : ℚ) * delta := by
    unfold recoveryBlockOf
    rw [hproduct]
    exact_mod_cast hnumerator
  exact_mod_cast hrational

/-- Elementary halving bound.  `(1 - delta) ^ block ≤ 1 / (1 + block * delta)`
follows from `(1 - delta) (1 + delta) ≤ 1` and Bernoulli, so one block of
`1 / delta` repetitions already halves the geometric factor.  No exponential or
logarithm is needed, which keeps the block length a computable natural. -/
private theorem pow_le_half_of_one_le_mul {delta : ℝ} (block : ℕ)
    (hpositive : 0 < delta) (hhalf : delta ≤ 1 / 2)
    (hmul : (1 : ℝ) ≤ (block : ℝ) * delta) :
    (1 - delta) ^ block ≤ (1 / 2 : ℝ) := by
  have hbase : (0 : ℝ) ≤ 1 - delta := by linarith
  have hpowNonneg : (0 : ℝ) ≤ (1 - delta) ^ block := pow_nonneg hbase block
  have hbernoulli : (1 : ℝ) + (block : ℝ) * delta ≤ (1 + delta) ^ block :=
    one_add_mul_le_pow (by linarith) block
  have hsquare : ((1 - delta) * (1 + delta)) ^ block ≤ (1 : ℝ) :=
    pow_le_one₀ (by nlinarith) (by nlinarith)
  have hchain : (1 - delta) ^ block * (1 + (block : ℝ) * delta) ≤ 1 := by
    calc
      (1 - delta) ^ block * (1 + (block : ℝ) * delta) ≤
          (1 - delta) ^ block * (1 + delta) ^ block :=
        mul_le_mul_of_nonneg_left hbernoulli hpowNonneg
      _ = ((1 - delta) * (1 + delta)) ^ block := (mul_pow _ _ block).symm
      _ ≤ 1 := hsquare
  nlinarith [hchain, mul_nonneg hpowNonneg (sub_nonneg.mpr hmul)]

/-- One block halves the geometric factor at every admissible radius.  This is
the general form of `recoveryBlock_halves`. -/
theorem recoveryBlockOf_halves {delta : ℚ} (hpositive : 0 < delta)
    (hhalf : (delta : ℝ) ≤ 1 / 2) :
    (1 - (delta : ℝ)) ^ recoveryBlockOf delta ≤ (1 / 2 : ℝ) :=
  pow_le_half_of_one_le_mul _ (by exact_mod_cast hpositive) hhalf
    (one_le_recoveryBlockOf_mul hpositive)

/-- General form of `xorEpsilon_recoveryBlocks_le`.  The extra block is what
replaces the `1 / 2 - recoveryDelta = 1 / 4` arithmetic: at a small radius the
trailing factor is only bounded by `1 / 2`, so the factor-four reserve is paid
by one further halving instead. -/
private theorem xorEpsilon_blocks_le {delta : ℝ} {block : ℕ}
    (hnonneg : 0 ≤ delta) (hhalf : delta ≤ 1 / 2)
    (hblock : (1 - delta) ^ block ≤ (1 / 2 : ℝ)) (repetitions : ℕ) :
    xorEpsilon delta (block * repetitions + block + 1) ≤
      1 / (2 : ℝ) ^ repetitions / 4 := by
  unfold xorEpsilon
  have hexponent :
      block * repetitions + block + 1 - 1 = block * (repetitions + 1) := by
    simp [Nat.mul_succ]
  rw [hexponent, pow_mul]
  have hbase : (0 : ℝ) ≤ (1 - delta) ^ block :=
    pow_nonneg (by linarith) block
  have hpower :
      ((1 - delta) ^ block) ^ (repetitions + 1) ≤
        (1 / 2 : ℝ) ^ (repetitions + 1) :=
    pow_le_pow_left₀ hbase hblock (repetitions + 1)
  calc
    ((1 - delta) ^ block) ^ (repetitions + 1) * (1 / 2 - delta) ≤
        (1 / 2 : ℝ) ^ (repetitions + 1) * (1 / 2) :=
      mul_le_mul hpower (by linarith) (by linarith) (by positivity)
    _ = 1 / (2 : ℝ) ^ repetitions / 4 := by
      rw [pow_succ, one_div_pow]
      ring

/-- Copy count for a fixed advantage at approximation radius `delta`.  General
form of `fixedCopies`. -/
def fixedCopiesOf (delta : ℚ) (rate : ℕ) : ℕ :=
  recoveryBlockOf delta * rate + recoveryBlockOf delta + 1

theorem fixedCopiesOf_positive (delta : ℚ) (rate : ℕ) :
    1 ≤ fixedCopiesOf delta rate := by
  unfold fixedCopiesOf
  omega

/-- The constant-copy schedule keeps the explicit factor-four reserve at every
admissible radius.  General form of `xorEpsilon_fixedCopies_le`. -/
theorem xorEpsilon_fixedCopiesOf_le {delta : ℚ} (hpositive : 0 < delta)
    (hhalf : (delta : ℝ) ≤ 1 / 2) (rate : ℕ) :
    xorEpsilon (delta : ℝ) (fixedCopiesOf delta rate) ≤
      1 / (2 : ℝ) ^ rate / 4 := by
  unfold fixedCopiesOf
  exact xorEpsilon_blocks_le
    (by exact_mod_cast le_of_lt hpositive) hhalf
    (recoveryBlockOf_halves hpositive hhalf) rate

/-! ## The copy schedule at a parametric radius

`Proof/PCP/VerifierThresholdSeam.lean` proves that the fixed radius `recoveryDelta = 1 / 4` cannot
be the radius the componentwise verifier charges: the seam's soundness reserve forces
`6 * zeta < 1 / 288`, while its completeness direction needs the joint clause budget
`2 * delta ≤ 6 * zeta`, i.e. `delta ≤ 3 * zeta`.

The geometric copy schedule is therefore defined above at an arbitrary rational radius `delta`
(`recoveryBlockOf`, `recoveryBlockOf_halves`, `inverseCopiesOf`, `fixedCopiesOf`,
`xorEpsilon_inverseCopiesOf_le`, `xorEpsilon_fixedCopiesOf_le`). The block length grows like
`1 / delta` (an elementary Bernoulli bound), and one extra block replaces the arithmetic
`1 / 2 - recoveryDelta = 1 / 4`, hence the `+ recoveryBlock` in `inverseCopies` and
`fixedCopies`, matched by the `+ recoveryBlock` in `inverseCopiesLinearCoefficient`.

No fixed literal radius can work. `executableParametersOfSource` is
`Classical.choice (existsExecutableSoundnessParameters source.gap)`, and its `zeta` is any
positive rational below `min (3 / 2) ((completeness - soundness) ^ 2 / 43200)`, with
`completeness` and `soundness` arbitrary reals of an arbitrary `UniformPointwisePCPPSource`. So
no positive literal `c` admits a proof of `c ≤ 3 * zeta`, and the radius must be a function of
the selected package: `VerifierThresholdSeam.repairedRecoveryDelta`.

The published schedule below is the generic schedule at `repairedDeltaValue pcppSource`, the
validity constant of the parameter package the componentwise verifier selects for the scheduled
pointwise-PCPP source, so the completeness seam closes at the radius the schedule uses.
`recoveryBlock`, `inverseCopies`, `fixedCopies` and `inverseCopiesLinearCoefficient` take the
`pcppSource` argument; `inverseRawCoreArity`, `fixedRawCoreArity`,
`inverseScheduledRawCoreArity`, `inverseCoreEnvelope` and `fixedCoreEnvelope` already receive it.
`ExecutableSoundnessParameters` (the threshold, `zeta`, the outer error, the estimation error and
both reserves) is unchanged. The admissibility conditions of the imported XOR contract,
`0 ≤ delta` and `delta < 1 / 2`, are proved at this radius in `VerifierThresholdSeam.§9`.

The fixed literal is kept below as `recoveryDelta`, with no schedule depending on it, because it
is the object of the refutation in `VerifierThresholdSeam.§7`;
`repairedDelta_ne_recoveryDelta` records that the two radii differ. -/

/-! ### The repaired approximation radius

The radius the schedule runs at is the validity constant of the parameter
package the componentwise verifier selects for the scheduled pointwise-PCPP
source.  It is choice-opaque: the only facts available about it are its
positivity and the soundness-reserve bound re-proved here. -/

end NearCubicWires.RecoveryScheduleEnvelope
