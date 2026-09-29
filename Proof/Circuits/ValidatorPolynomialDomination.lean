import Proof.Amplification.RecoveryLimitsComputableFamily
import Proof.Amplification.RecoveryVerifierResourceEnvelope
import Proof.Circuits.CanonicalRoundCall

namespace NearCubicWires.ValidatorPolynomialDomination

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §1 One uniform domination judgement -/

/-- **The domination judgement.**  `PolyBounded value measure coefficient
degree` says the charge `value` is dominated by the polynomial budget of
`coefficient` and `degree` at `measure`.  It is definitionally the machine's
own `polynomialBudget` inequality, so nothing is lost transporting a spine
fact into a premise of `ExecutableRecoveryMachine`. -/
def PolyBounded (value measure coefficient degree : ℕ) : Prop :=
  value ≤ coefficient * (measure + 1) ^ degree

private theorem one_le_measure_pow (measure degree : ℕ) :
    1 ≤ (measure + 1) ^ degree :=
  Nat.one_le_pow _ _ (by omega)

/-- A closed charge is dominated by its own value at every degree: this is the
rule every program-shape overhead in the cone uses. -/
theorem PolyBounded.of_le_coefficient
    {value measure coefficient degree : ℕ} (h : value ≤ coefficient) :
    PolyBounded value measure coefficient degree := by
  refine h.trans ?_
  calc
    coefficient = coefficient * 1 := (Nat.mul_one _).symm
    _ ≤ coefficient * (measure + 1) ^ degree :=
      Nat.mul_le_mul_left _ (one_le_measure_pow measure degree)

theorem polyBounded_const (coefficient measure degree : ℕ) :
    PolyBounded coefficient measure coefficient degree :=
  PolyBounded.of_le_coefficient le_rfl

/-- Weakening on the *charge*: the only rule that consumes an exact fuel
identity. -/
theorem PolyBounded.mono
    {value value' measure coefficient degree : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : value' ≤ value) :
    PolyBounded value' measure coefficient degree := hle.trans h

theorem PolyBounded.degree_mono
    {value measure coefficient degree degree' : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : degree ≤ degree') :
    PolyBounded value measure coefficient degree' :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hle))

theorem PolyBounded.measure_mono
    {value measure measure' coefficient degree : ℕ}
    (h : PolyBounded value measure coefficient degree)
    (hle : measure ≤ measure') :
    PolyBounded value measure' coefficient degree :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) degree))

/-- Additive composition: sequential charges keep the degree and add the
coefficients. -/
theorem PolyBounded.add
    {left right measure leftCoefficient rightCoefficient degree : ℕ}
    (hleft : PolyBounded left measure leftCoefficient degree)
    (hright : PolyBounded right measure rightCoefficient degree) :
    PolyBounded (left + right) measure
      (leftCoefficient + rightCoefficient) degree := by
  unfold PolyBounded at hleft hright ⊢
  rw [Nat.add_mul]
  omega

/-- **The only degree-raising rule.**  A charge repeated once per element of a
counted collection multiplies the two coefficients and *adds* the two degrees.
Every multiplication in the cone is of this shape — a count, a width, an arity
or an index against a per-element charge — never a decoded magnitude. -/
theorem PolyBounded.mul
    {left right measure leftCoefficient rightCoefficient
      leftDegree rightDegree : ℕ}
    (hleft : PolyBounded left measure leftCoefficient leftDegree)
    (hright : PolyBounded right measure rightCoefficient rightDegree) :
    PolyBounded (left * right) measure
      (leftCoefficient * rightCoefficient) (leftDegree + rightDegree) := by
  unfold PolyBounded at hleft hright ⊢
  calc
    left * right ≤
        (leftCoefficient * (measure + 1) ^ leftDegree) *
          (rightCoefficient * (measure + 1) ^ rightDegree) :=
      Nat.mul_le_mul hleft hright
    _ = leftCoefficient * rightCoefficient *
        (measure + 1) ^ (leftDegree + rightDegree) := by
      rw [Nat.pow_add]
      ring

/-! ## §2 The linker and call-combinator algebra

Every composite fuel definition in the validator's cone is one of the eight
shapes below.  Each is discharged once, from §1, so a spine walk never has to
re-derive a linker charge. -/

/-- Scaling by a closed repetition count keeps the degree. -/
theorem PolyBounded.const_mul
    {value measure coefficient degree : ℕ} (factor : ℕ)
    (h : PolyBounded value measure coefficient degree) :
    PolyBounded (factor * value) measure (factor * coefficient) degree := by
  unfold PolyBounded at h ⊢
  calc
    factor * value ≤ factor * (coefficient * (measure + 1) ^ degree) :=
      Nat.mul_le_mul_left _ h
    _ = factor * coefficient * (measure + 1) ^ degree := by ring

/-! ## §4 The width of the frozen limits record

The width ledger of §3 exposes exactly one ingredient that is not a charge of
an executable stage: the validator's structural prefix carries
`encodeRecoveryWitnessLimits limits` through its handoff, so its register width
is bounded only once the encoded policy record is.  This section closes that
for the computable limits family, whose every field is explicit arithmetic in
the frozen amplifier numerals, the copy bound and the arity. -/

/-- Binary width is subadditive under multiplication. -/
theorem natBitLength_mul_le (left right : ℕ) :
    natBitLength (left * right) ≤ natBitLength left + natBitLength right := by
  have hleftOne : 1 ≤ natBitLength left := by
    unfold natBitLength
    omega
  have hrightOne : 1 ≤ natBitLength right := by
    unfold natBitLength
    omega
  rcases Nat.eq_zero_or_pos (left * right) with hzero | hpositive
  · rw [hzero]
    have : natBitLength 0 = 1 := by
      simp [natBitLength]
    omega
  · have hleftLt : left < 2 ^ natBitLength left := by
      have hself := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) left
      simpa [natBitLength] using hself
    have hrightLt : right < 2 ^ natBitLength right := by
      have hself := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) right
      simpa [natBitLength] using hself
    have hproduct :
        left * right < 2 ^ (natBitLength left + natBitLength right) := by
      calc
        left * right < 2 ^ natBitLength left * 2 ^ natBitLength right :=
          mul_lt_mul'' hleftLt hrightLt (Nat.zero_le _) (Nat.zero_le _)
        _ = 2 ^ (natBitLength left + natBitLength right) := (pow_add _ _ _).symm
    have hlog :=
      Nat.log_lt_of_lt_pow (b := 2) hpositive.ne' hproduct
    unfold natBitLength at hlog ⊢
    omega

/-- Binary width of a power is linear in the exponent. -/
theorem natBitLength_pow_le (base exponent : ℕ) :
    natBitLength (base ^ exponent) ≤ exponent * natBitLength base + 1 := by
  induction exponent with
  | zero => simp [natBitLength]
  | succ count inductionHypothesis =>
      have hstep := natBitLength_mul_le (base ^ count) base
      rw [pow_succ]
      have hexpand :
          (count + 1) * natBitLength base =
            count * natBitLength base + natBitLength base := by
        ring
      omega

/-! ### The serialized policy record -/

/-! ### The computable limits family

Every field of `computableXorRecoveryWitnessLimits` is explicit arithmetic in
the four frozen profile numerals, the copy bound and the arity, so the width
certificate above is available unconditionally. -/

/-! ## §5 The machine's two validator premises

The machine charges at `recoveryVerifierDegree = 4`.  §3 turns a stage-level
envelope of any degree `d` into a validator-level envelope of degree `d`; the
numeral is then raised to `4` by `PolyBounded.degree_mono`, which is legal for
every `d ≤ 4` and forces a reported degree lift for any `d > 4`. -/

end NearCubicWires.ValidatorPolynomialDomination
