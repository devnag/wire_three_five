import Proof.Circuits.AggregateSemanticStage
import Proof.Circuits.ComponentwisePolynomial
import Proof.Supplier.SupplierEstimator

/-!
# The linearity expansion of the aggregate clause mean

`AggregateSemanticStage` closes the corrected semantic stage down to one
obligation, `AggregateEstimateAccurate`: the machine must produce a number
within `estimationError` of

```text
mu = E_{i,u} F_i(T(u))
```

where `F_i` is the manuscript's degree-two arithmetization of PCPP clause `i`
and `T(u)` is the proof vector recovered from the guessed legal circuit sum at
PCPP input `u`.  This module builds the bridge from the supplier estimator's
per-request conjunction probabilities to that one number, which is Appendix
C.10's sentence "the machine estimates `mu` **by expanding it into AND-four
supplier calls**".

## §0 What the expansion produces

Three structures compose, and each of them is *linear*:

* the guessed sum is `D = sum_a alpha_a C_a`, linear in its atoms;
* fixing a clause address and a side is a **literal restriction** of every
  atom (`SliceRestricts` below), so on each occurrence slice the guess is one
  linear polynomial in circuits of the supplier's own family at arity `n`;
* the recovered proof coordinate is the **occurrence-fibre average** of the
  signed slice readings, again linear.

Only the clause polynomial `L + R - L*R` is nonlinear, and it is nonlinear of
degree exactly two.  Consequently **every** monomial of the expansion carries
at most two restricted atoms: the conjunctions that arise are the empty
conjunction (the constant, `conjunctionProbability evaluate []` = 1),
singletons `[C]`, and pairs `[C, C']`.  All three are inside the supplier's
`circuits.length <= 4` ABI, so no shape the expansion produces is outside what
`SharedNormalizedEstimator` can express.  The four-atom conjunctions of the
manuscript come from the *validity* side (`T^2 (1-T)^2`), which the seam
charges separately; the estimated clause mean itself never needs more than a
pair.

## §1 The bookkeeping

`ComponentwisePolynomial` already owns the monomial calculus: `clausePolynomial`
is the degree-two clause, `literalPolynomial` is the sign, `CircuitPolynomial.mul`
appends factor lists, and `estimatedMean_error_le` is the componentwise error
ledger.  Only one constructor is missing — a *finite* sum of polynomials, needed
by the occurrence fibre and by the clause-index average — and §1 supplies it.

## §2 The expansion

`aggregateClausePolynomial` is the composite, and
`aggregateClauseMean_eq_sum_conjunctionProbability` is the exact algebraic
identity: the aggregate clause mean *is* the coefficient-weighted sum of
conjunction probabilities of restricted atom lists of length at most two.

## §3 The coefficient mass

`clauseMassCap` is the manuscript's `Lambda_0`: with per-slice coefficient mass
at most `Lambda`, the aggregate expansion has coefficient mass at most
`(2 + Lambda)^2 + 2 * (2 + Lambda)`.  The two additive `1`s are the two signs —
the occurrence table stores the *signed* literal value, and the clause
polynomial re-applies the sign — and the square is the single product.  In the
manuscript's notation `Lambda_0 <= 4 * augmented^2 + 4 * augmented`, comfortably
inside the published `augmented^4`.

## §4 The recombination and the numeric dial

`aggregateEstimate_error_le_of_expansion` is `componentwise_real_error` at
`error := rows.failure`, `mass := Lambda_0`;
`aggregate_estimatedMean_error_le` is its instance at the concrete expansion.
`massCap_advantage_le_estimationError` is the numeric dial: at the published
request `D > 4R + 10` of Appendix C.3/A.8, the inverse-polynomial supplier
advantage times `Lambda_0(q)` is eventually below any fixed positive
`estimationError`.

## §5 The stage

`aggregateEstimateAccurate_of_expansion` discharges
`AggregateSemanticStage.AggregateEstimateAccurate`, and the two stage-side
corollaries put the completeness comparison and the soundness contradiction
each behind one named hypothesis about the executed supplier aggregation.
-/

namespace NearCubicWires.AggregateClauseExpansion

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.OccurrenceSliceTransport
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

/-! ## §1 Finite sums of circuit polynomials -/

/-- Concatenating monomial lists adds polynomials.  This is the finite-sum
constructor the occurrence fibre and the clause-index average both need;
`CircuitPolynomial.add` is its two-element case. -/
def polynomialSumList {Atom : Type} {degree : ℕ}
    (polynomials : List (CircuitPolynomial Atom degree)) :
    CircuitPolynomial Atom degree where
  monomials := polynomials.flatMap fun polynomial => polynomial.monomials

theorem polynomialSumList_value {Atom : Type} {degree q : ℕ}
    (evaluate : Atom → BitInput q → Bool)
    (polynomials : List (CircuitPolynomial Atom degree))
    (input : BitInput q) :
    (polynomialSumList polynomials).value evaluate input =
      (polynomials.map fun polynomial =>
        polynomial.value evaluate input).sum := by
  change
    (((polynomials.flatMap fun polynomial => polynomial.monomials).map
        fun monomial => monomial.value evaluate input).sum) =
      (polynomials.map fun polynomial =>
        polynomial.value evaluate input).sum
  induction polynomials with
  | nil => rfl
  | cons polynomial polynomials inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, inductionHypothesis]
      rfl

theorem polynomialSumList_coefficientMass {Atom : Type} {degree : ℕ}
    (polynomials : List (CircuitPolynomial Atom degree)) :
    (polynomialSumList polynomials).coefficientMass =
      (polynomials.map fun polynomial =>
        polynomial.coefficientMass).sum := by
  change
    (((polynomials.flatMap fun polynomial => polynomial.monomials).map
        fun monomial => |monomial.coefficient|).sum) =
      (polynomials.map fun polynomial => polynomial.coefficientMass).sum
  induction polynomials with
  | nil => rfl
  | cons polynomial polynomials inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, inductionHypothesis]
      rfl

/-- Sum a family of polynomials over a finite index set. -/
noncomputable def polynomialFinsetSum {Atom : Type} {degree : ℕ} {ι : Type}
    (index : Finset ι) (polynomial : ι → CircuitPolynomial Atom degree) :
    CircuitPolynomial Atom degree :=
  polynomialSumList (index.toList.map polynomial)

theorem polynomialFinsetSum_value {Atom : Type} {degree q : ℕ} {ι : Type}
    (evaluate : Atom → BitInput q → Bool) (index : Finset ι)
    (polynomial : ι → CircuitPolynomial Atom degree) (input : BitInput q) :
    (polynomialFinsetSum index polynomial).value evaluate input =
      ∑ i ∈ index, (polynomial i).value evaluate input := by
  rw [polynomialFinsetSum, polynomialSumList_value, List.map_map]
  exact Finset.sum_map_toList index
    (fun i => (polynomial i).value evaluate input)

theorem polynomialFinsetSum_coefficientMass {Atom : Type} {degree : ℕ}
    {ι : Type} (index : Finset ι)
    (polynomial : ι → CircuitPolynomial Atom degree) :
    (polynomialFinsetSum index polynomial).coefficientMass =
      ∑ i ∈ index, (polynomial i).coefficientMass := by
  rw [polynomialFinsetSum, polynomialSumList_coefficientMass, List.map_map]
  exact Finset.sum_map_toList index
    (fun i => (polynomial i).coefficientMass)

theorem coefficientMass_nonneg {Atom : Type} {degree : ℕ}
    (polynomial : CircuitPolynomial Atom degree) :
    0 ≤ polynomial.coefficientMass := by
  refine List.sum_nonneg ?_
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨monomial, _, hcoefficient⟩
  rw [← hcoefficient]
  exact abs_nonneg _

/-! ## §2 The expansion

The three linear layers, then the single degree-two clause. -/

/-! ## §3 The coefficient mass

`Lambda_0` in the manuscript's notation.  Two signs and one product. -/

/-! ## §4 The recombination

`componentwise_real_error` at `error := rows.failure`, `mass := Lambda_0`. -/

/-! ## §5 The numeric dial

Appendix C.3 requests `D > 4R + 10` from the supplier, where `R` bounds the
coefficient-mass exponent and `D` the accuracy exponent.  At that request the
propagated error of the expansion is eventually below any fixed positive
`estimationError`. -/

/-! ## §6 Discharging the stage obligation -/

end NearCubicWires.AggregateClauseExpansion
