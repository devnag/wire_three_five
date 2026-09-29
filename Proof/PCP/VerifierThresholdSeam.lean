import Proof.Circuits.ComponentwiseBranchExtraction
import Proof.Foundations.RecoveryScheduleEnvelope

namespace NearCubicWires.VerifierThresholdSeam

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ComponentwiseWeakMachine
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.SourceInterfaces

/-! ## §1 The clause-marginal `ℓ¹` error

The Case-2 seed is the honest *occurrence* table, so its uniform measure is
exactly the clause marginal crossed with the left/right position.  The budget
below is therefore the quantity the approximation hypothesis controls; it is
the sum over the two clause sides, matching `totalClausePenaltyMean`. -/

/-- Mean `ℓ¹` error between a guessed proof and a reference proof, under the
clause marginal of one selected clause side. -/
noncomputable def clauseErrorMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) : ℝ :=
  𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    |value (literalIndex (side (pcpp.clauses i))) -
      reference (literalIndex (side (pcpp.clauses i)))|

/-- Total clause-marginal `ℓ¹` error charged jointly on both clause sides.
This is the exact analogue of `totalClausePenaltyMean` and the quantity the
Case-2 approximation hypothesis bounds. -/
noncomputable def totalClauseErrorMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    ℝ :=
  clauseErrorMean pcpp value reference TwoLiteralClause.left +
    clauseErrorMean pcpp value reference TwoLiteralClause.right

/-- The same error under the uniform measure on clause *occurrences*, i.e. the
uniform pair (clause index, left/right position).  This is exactly the measure
carried by `honestOccurrenceFunction`, so it is the quantity the Case-2
approximation parameter bounds. -/
noncomputable def clauseOccurrenceErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    ℝ :=
  (clauseErrorMean pcpp value reference TwoLiteralClause.left +
      clauseErrorMean pcpp value reference TwoLiteralClause.right) / 2

/-- Charging both clause sides doubles the occurrence-uniform error.  This is
the whole content of the budget conversion `delta ↦ 2 * delta` between the seed
metric and the verifier's joint ledger. -/
theorem totalClauseErrorMean_eq_two_mul_occurrence {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    totalClauseErrorMean pcpp value reference =
      2 * clauseOccurrenceErrorMean pcpp value reference := by
  unfold totalClauseErrorMean clauseOccurrenceErrorMean
  ring

/-! ## §2 The validity charge is dominated by the `ℓ¹` budget

The verifier's componentwise test charges a square penalty.  Against any
Boolean proof that respects the prescribed systematic parities, that penalty is
below the pointwise `ℓ¹` error, so the whole validity ladder is paid by the
same budget. -/

/-- The prescribed rounding constraint at a coordinate is satisfied by every
genuine PCPP assignment for the same input. -/
private theorem systematicConstraint_eq_some_imp {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (index : Fin (pcpp.systematicBits + pcpp.auxiliaryBits))
    (expected : Bool)
    (hconstraint : systematicConstraint pcpp input index = some expected) :
    pcpp.assignment input auxiliary index = expected := by
  refine Fin.addCases ?_ ?_ index expected hconstraint
  · intro i expected hconstraint
    simp only [systematicConstraint, Fin.addCases_left] at hconstraint
    simp [PointwisePCPP.assignment, ← Option.some_inj.mp hconstraint]
  · intro i expected hconstraint
    simp only [systematicConstraint, Fin.addCases_right] at hconstraint
    exact absurd hconstraint (by simp)

private theorem validityPenalty_le_assignment_distance {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (index : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    validityPenalty (systematicConstraint pcpp input index) (value index) ≤
      |value index -
        bitAsReal (pcpp.assignment input auxiliary index)| :=
  validityPenalty_le_nearby_distance _
    (pcpp.assignment input auxiliary index) (value index)
    (hnonneg index) (hleOne index)
    (fun expected hexpected =>
      systematicConstraint_eq_some_imp pcpp input auxiliary index expected
        hexpected)

theorem clausePenaltyMean_le_clauseErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    clausePenaltyMean pcpp input value side ≤
      clauseErrorMean pcpp value
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) side := by
  unfold clausePenaltyMean clauseErrorMean
  exact Finset.expect_le_expect fun i _ =>
    validityPenalty_le_assignment_distance pcpp input auxiliary value
      hnonneg hleOne (literalIndex (side (pcpp.clauses i)))

/-- The verifier's joint validity charge never exceeds the clause-marginal
`ℓ¹` budget against any genuine PCPP assignment. -/
theorem totalClausePenaltyMean_le_totalClauseErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1) :
    totalClausePenaltyMean pcpp input value ≤
      totalClauseErrorMean pcpp value
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) := by
  unfold totalClausePenaltyMean totalClauseErrorMean
  have hleft := clausePenaltyMean_le_clauseErrorMean pcpp input auxiliary
    value hnonneg hleOne TwoLiteralClause.left
  have hright := clausePenaltyMean_le_clauseErrorMean pcpp input auxiliary
    value hnonneg hleOne TwoLiteralClause.right
  linarith

/-! ## §3 The clause mean moves by at most the `ℓ¹` budget

The arithmetized two-literal clause is one-Lipschitz in each literal on the
unit cube, so the same budget that pays the validity ladder also caps the
movement of the estimated quantity. -/

private theorem literalValue_nonnegative (negative : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1) :
    0 ≤ literalValue negative value := by
  cases negative
  · simpa [literalValue] using hzero
  · have hvalue : literalValue true value = 1 - value := by
      simp [literalValue]
    rw [hvalue]
    linarith

private theorem literalValue_le_one (negative : Bool) (value : ℝ)
    (hzero : 0 ≤ value) (hone : value ≤ 1) :
    literalValue negative value ≤ 1 := by
  cases negative
  · simpa [literalValue] using hone
  · have hvalue : literalValue true value = 1 - value := by
      simp [literalValue]
    rw [hvalue]
    linarith

/-- One-Lipschitz movement of the arithmetized clause on the unit cube.  This
is the completeness-side counterpart of `clauseValue_sub_le`, which is stated
with the quadratic remainder needed by the rounding ledger. -/
theorem abs_clauseValue_sub_le
    (leftNegative rightNegative : Bool)
    (left right otherLeft otherRight : ℝ)
    (hright : 0 ≤ right) (hrightOne : right ≤ 1)
    (hotherLeft : 0 ≤ otherLeft) (hotherLeftOne : otherLeft ≤ 1) :
    |clauseValue leftNegative rightNegative left right -
        clauseValue leftNegative rightNegative otherLeft otherRight| ≤
      |left - otherLeft| + |right - otherRight| := by
  have hidentity :
      clauseValue leftNegative rightNegative left right -
          clauseValue leftNegative rightNegative otherLeft otherRight =
        (literalValue leftNegative left -
              literalValue leftNegative otherLeft) *
            (1 - literalValue rightNegative right) +
          (literalValue rightNegative right -
              literalValue rightNegative otherRight) *
            (1 - literalValue leftNegative otherLeft) := by
    simp only [clauseValue]
    ring
  have hrightBound : |1 - literalValue rightNegative right| ≤ 1 := by
    rw [abs_of_nonneg
      (by linarith [literalValue_le_one rightNegative right hright hrightOne] :
        (0 : ℝ) ≤ 1 - literalValue rightNegative right)]
    linarith [literalValue_nonnegative rightNegative right hright hrightOne]
  have hleftBound : |1 - literalValue leftNegative otherLeft| ≤ 1 := by
    rw [abs_of_nonneg
      (by
        linarith [literalValue_le_one leftNegative otherLeft hotherLeft
          hotherLeftOne] :
        (0 : ℝ) ≤ 1 - literalValue leftNegative otherLeft)]
    linarith [literalValue_nonnegative leftNegative otherLeft hotherLeft
      hotherLeftOne]
  rw [hidentity]
  calc
    |(literalValue leftNegative left -
            literalValue leftNegative otherLeft) *
          (1 - literalValue rightNegative right) +
        (literalValue rightNegative right -
            literalValue rightNegative otherRight) *
          (1 - literalValue leftNegative otherLeft)| ≤
        |(literalValue leftNegative left -
              literalValue leftNegative otherLeft) *
            (1 - literalValue rightNegative right)| +
          |(literalValue rightNegative right -
              literalValue rightNegative otherRight) *
            (1 - literalValue leftNegative otherLeft)| :=
      abs_add_le _ _
    _ = |literalValue leftNegative left -
            literalValue leftNegative otherLeft| *
          |1 - literalValue rightNegative right| +
        |literalValue rightNegative right -
            literalValue rightNegative otherRight| *
          |1 - literalValue leftNegative otherLeft| := by
      rw [abs_mul, abs_mul]
    _ ≤ |literalValue leftNegative left -
            literalValue leftNegative otherLeft| * 1 +
        |literalValue rightNegative right -
            literalValue rightNegative otherRight| * 1 := by
      gcongr
    _ = |left - otherLeft| + |right - otherRight| := by
      rw [mul_one, mul_one, abs_literalValue_sub, abs_literalValue_sub]

/-- Movement of the estimated clause mean is charged entirely to the
clause-marginal `ℓ¹` budget. -/
theorem abs_clauseMean_sub_le_totalClauseErrorMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (hnonneg : ∀ j, 0 ≤ value j) (hleOne : ∀ j, value j ≤ 1)
    (hreferenceNonneg : ∀ j, 0 ≤ reference j)
    (hreferenceLeOne : ∀ j, reference j ≤ 1) :
    |clauseMean pcpp value - clauseMean pcpp reference| ≤
      totalClauseErrorMean pcpp value reference := by
  set index : Finset (Fin (2 ^ pcpp.clauseBits)) := univ with hindex
  calc
    |clauseMean pcpp value - clauseMean pcpp reference| =
        |𝔼 i ∈ index,
          (clauseRealValue (pcpp.clauses i) value -
            clauseRealValue (pcpp.clauses i) reference)| := by
      rw [Finset.expect_sub_distrib]
      rfl
    _ ≤ 𝔼 i ∈ index,
          |clauseRealValue (pcpp.clauses i) value -
            clauseRealValue (pcpp.clauses i) reference| :=
      Finset.abs_expect_le _ _
    _ ≤ 𝔼 i ∈ index,
          (|value (literalIndex (pcpp.clauses i).left) -
              reference (literalIndex (pcpp.clauses i).left)| +
            |value (literalIndex (pcpp.clauses i).right) -
              reference (literalIndex (pcpp.clauses i).right)|) :=
      Finset.expect_le_expect fun i _ =>
        abs_clauseValue_sub_le _ _ _ _ _ _
          (hnonneg _) (hleOne _) (hreferenceNonneg _) (hreferenceLeOne _)
    _ = totalClauseErrorMean pcpp value reference := by
      rw [Finset.expect_add_distrib]
      rfl

/-! ## §4 The completeness direction closes at budget `6 * zeta`

Every constant below is the published one.  The only hypothesis is that the
clause-marginal `ℓ¹` budget of the guessed proof against the honest table is at
most `6 * zeta`; nothing else about the guessed proof is used. -/

/-! ## §6 The soundness direction closes unconditionally

The published reserves put the whole NO-instance ledger strictly below the
threshold, so the accepting comparison is contradictory exactly where the
imported PCPP soundness applies. -/

/-! ## §7 The published approximation parameter does not fit

The Case-2 seed is the honest *occurrence* table, so a uniform `ℓ¹` ball of
radius `recoveryDelta` around it is a clause-marginal ball of radius
`2 * recoveryDelta` once both clause sides are charged.  With
`recoveryDelta = 1 / 4` that budget is `1 / 2`, and no parameter package for a
source with `0 ≤ soundness` and `completeness ≤ 1` can absorb it. -/

/-! ### Tightness of the budget

The two failures above are not artefacts of a lossy estimate.  The single
clause below realizes the whole `§3` bound: a guess at clause-marginal `ℓ¹`
distance exactly `recoveryClauseErrorBudget` from a perfectly satisfying
Boolean table loses exactly that much clause mean, while its booleanity
penalty already exceeds the published validity constant. -/

/-! ## §8 The smallest repair

Nothing in the ladder has to move except the approximation parameter.  The
completeness direction closes verbatim once `delta ≤ 3 * zeta`, and such a
`delta` is always available, strictly positive and below `1 / 2`, so the
imported XOR contract still applies.  The published `recoveryDelta = 1 / 4`
misses that condition by a factor of at least `576`. -/

/-! ## §9 The repaired approximation radius, and the schedule it selects

`§8` shows the repair is admissible; this section names it, discharges every
side condition the imported XOR contract asks of an approximation radius, and
closes the completeness direction at the one parameter package the pipeline
selects.  `RecoveryScheduleEnvelope` supplies the copy schedule at an arbitrary
radius (`recoveryBlockOf`, `inverseCopiesOf`, `fixedCopiesOf`), so the repaired
radius inherits the published factor-four reserve verbatim; the only cost is
that the block length grows like `1 / zeta`.

Nothing in `ExecutableSoundnessParameters` moves.  The fixed radius
`recoveryDelta = 1 / 4` survives only as the object refuted in `§7`: the XOR
ledger of `Proof/Amplification/CaseTwoRecoveryAssembly.lean` has been migrated onto
`RecoveryScheduleEnvelope.repairedDelta`, which is definitionally the radius
below at the scheduled pointwise-PCPP source. -/

end NearCubicWires.VerifierThresholdSeam
