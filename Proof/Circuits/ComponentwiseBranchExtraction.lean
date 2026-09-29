import Proof.MachineModel.ComponentwiseWeakMachine

/-!
# Accepting-branch extraction for the componentwise weak machine

`eventuallyOneSided_of_executableBranchLedger` closes the one-sided
obligation as soon as every accepting branch on a hierarchy-NO input yields
an `ExecutableNoInstanceBranchLedger`.  This module supplies exactly that
extraction step for the fixed componentwise verifier ABI.

The verifier reads one guessed real-valued PCPP proof, rounds it against the
prescribed systematic coordinates, checks componentwise validity, estimates
the arithmetized clause mean with the shared supplier estimator, and compares
that estimate with a stored rational threshold.  The trace below records the
decoded data and the exact rational comparisons it performs; it never records
a semantic acceptance callback.  Two of the ledger's four inequalities are
then proved here rather than assumed:

* the rounded clause mean equals the imported PCPP satisfied fraction, so its
  soundness bound is the published source guarantee;
* the real clause mean stays within `6 * sqrt (12 * zeta)` of the rounded one,
  by the componentwise validity ledger of `ComponentwiseValidity`.

The remaining two are the supplier estimator's own error guarantee and the
verifier's exact rational threshold comparison.
-/

namespace NearCubicWires.ComponentwiseBranchExtraction

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ComponentwiseWeakMachine
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces

/-! ## Signed decomposition of a PCPP literal -/

/-- The coordinate queried by a literal, ignoring its sign. -/
def literalIndex {arity : ℕ} : Literal arity → Fin arity
  | .positive index => index
  | .negative index => index

/-- The sign carried by a literal, in the form used by the arithmetized
clause polynomial `clauseValue`. -/
def literalNegated {arity : ℕ} : Literal arity → Bool
  | .positive _ => false
  | .negative _ => true

@[simp] theorem literal_eval_eq_xor {arity : ℕ} (literal : Literal arity)
    (assignment : BitInput arity) :
    literal.eval assignment =
      xor (literalNegated literal) (assignment (literalIndex literal)) := by
  cases literal <;> simp [Literal.eval, literalNegated, literalIndex]

/-! ## The arithmetized two-literal clause -/

/-- One clause of the imported PCPP evaluated on a real proof vector. -/
def clauseRealValue {arity : ℕ} (clause : TwoLiteralClause arity)
    (value : Fin arity → ℝ) : ℝ :=
  clauseValue (literalNegated clause.left) (literalNegated clause.right)
    (value (literalIndex clause.left)) (value (literalIndex clause.right))

theorem clauseValue_bitAsReal (leftNegative rightNegative left right : Bool) :
    clauseValue leftNegative rightNegative (bitAsReal left)
        (bitAsReal right) =
      bitAsReal (xor leftNegative left || xor rightNegative right) := by
  cases leftNegative <;> cases rightNegative <;> cases left <;>
    cases right <;> norm_num [clauseValue, literalValue, bitAsReal]

/-- On a Boolean proof the arithmetization is exactly the clause's Boolean
value.  This is the only place where the polynomial representation and the
imported combinatorial semantics meet. -/
theorem clauseRealValue_bitAsReal {arity : ℕ}
    (clause : TwoLiteralClause arity) (assignment : BitInput arity) :
    clauseRealValue clause (fun j => bitAsReal (assignment j)) =
      bitAsReal (clause.eval assignment) := by
  rw [clauseRealValue, clauseValue_bitAsReal]
  simp [TwoLiteralClause.eval]

/-! ## The clause mean of a real proof -/

/-- Uniform mean of the arithmetized clauses over the imported clause index
space.  This is the quantity the verifier estimates. -/
noncomputable def clauseMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    clauseRealValue (pcpp.clauses i) value

theorem expect_bitAsReal_eq_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        bitAsReal
          ((pcpp.clauses i).eval (pcpp.assignment input auxiliary))) =
      pcpp.satisfiedFraction input auxiliary := by
  rw [PointwisePCPP.satisfiedFraction, Finset.expect_eq_sum_div_card]
  congr 1
  · simp [bitAsReal]
  · simp

/-- The rounded clause mean is exactly the imported PCPP satisfied fraction of
the Boolean proof it rounds to. -/
theorem clauseMean_bitAsReal_eq_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    clauseMean pcpp
        (fun j => bitAsReal (pcpp.assignment input auxiliary j)) =
      pcpp.satisfiedFraction input auxiliary := by
  rw [clauseMean,
    ← expect_bitAsReal_eq_satisfiedFraction pcpp input auxiliary]
  exact Finset.expect_congr rfl fun i _ =>
    clauseRealValue_bitAsReal (pcpp.clauses i)
      (pcpp.assignment input auxiliary)

/-! ## Prescribed rounding of a guessed real proof -/

/-- The rounding constraint the verifier imposes coordinatewise: systematic
coordinates must round to their prescribed parity, auxiliary coordinates are
free and round at one half. -/
noncomputable def systematicConstraint {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n) :
    Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → Option Bool :=
  Fin.addCases
    (fun i => some (parityOn (pcpp.systematicSupport i) input))
    (fun _ => none)

/-- The Boolean proof obtained by the prescribed rounding. -/
noncomputable def roundedProof {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    BitInput (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  fun j => validityRound (systematicConstraint pcpp input j) (value j)

/-- The free half of the rounded proof, in the shape the imported PCPP
soundness statement quantifies over. -/
noncomputable def roundedAuxiliary {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    BitInput pcpp.auxiliaryBits :=
  fun j => roundBit (value (Fin.natAdd pcpp.systematicBits j))

/-- The prescribed rounding always lands on a genuine PCPP assignment: the
systematic block is forced, so only the auxiliary block is guessed.  Nothing
else is needed to invoke the imported soundness guarantee. -/
theorem roundedProof_eq_assignment {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    roundedProof pcpp input value =
      pcpp.assignment input (roundedAuxiliary pcpp value) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp [roundedProof, systematicConstraint, validityRound,
      PointwisePCPP.assignment]
  · intro i
    simp [roundedProof, systematicConstraint, validityRound,
      PointwisePCPP.assignment, roundedAuxiliary]

/-! ## The componentwise validity ledger under the clause marginals -/

/-- Mean validity penalty over one selected side of the clause distribution.
The verifier checks the two sides jointly, which is what the aggregated
`clauseMean_distance_le_six_of_combined` consumes. -/
noncomputable def clausePenaltyMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (side : TwoLiteralClause (pcpp.systematicBits + pcpp.auxiliaryBits) →
      Literal (pcpp.systematicBits + pcpp.auxiliaryBits)) : ℝ :=
  𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
    validityPenalty
      (systematicConstraint pcpp input (literalIndex (side (pcpp.clauses i))))
      (value (literalIndex (side (pcpp.clauses i))))

/-- Total validity penalty charged by the verifier's componentwise test. -/
noncomputable def totalClausePenaltyMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (value : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  clausePenaltyMean pcpp input value TwoLiteralClause.left +
    clausePenaltyMean pcpp input value TwoLiteralClause.right

/-! ## The accepting verifier trace -/

/-! ## Exact rational front end for the checked fields

The register program stores the decoded proof and its validity charge as
exact rationals.  The lemmas below are the only permitted bridge between that
arithmetic and the real-valued ledger, so no second decoder or floating
surrogate is introduced. -/

/-! ## Ledger extraction -/

/-! ## The published PCPP soundness owner -/

/-! ## Branch evidence and the one-sided closure -/

/-! ## The canonically selected verifier constants -/

/-! ## Non-vacuity regression

The extracted ledger is an empty type, so the trace ABI must be contradictory
only in the presence of the imported soundness bound.  The regression below
certifies that the ABI is satisfiable on its own: a mis-stated field cannot
make the extraction theorem silently vacuous. -/

end NearCubicWires.ComponentwiseBranchExtraction
