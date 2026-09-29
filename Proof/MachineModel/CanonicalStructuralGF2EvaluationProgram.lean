import Proof.Circuits.CanonicalForkCall
import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBalancedTraversalParityProgram
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.MachineModel.CanonicalNativeCallProgram

/-!
# Executing structural `𝔽₂` polynomials on the oracle machine

`CanonicalFourfoldRowProgram` fixes the structural polynomial representation
used by every canonical row: a `List (List ℕ)` whose inner lists are monomials
of shared residual-variable codes, and whose evaluation
`evaluateStructuralGF2` is the parity of the number of satisfied monomials.
Nothing in the repository executed that evaluation; the row evaluator needs it.

This module supplies the missing machine.  Only two facts about the
representation are used:

* a monomial is satisfied exactly when no variable in it is false, so the
  conjunction is the zero test of one balanced natural sum;
* a polynomial's value is the parity of its monomial bits, which is precisely
  the fixed balanced parity fold already verified for Case 2 seeds.

The assignment stays a link-time program parameter with an exact interpreter
premise and no fuel or callback argument, exactly as the row tail keeps its
`rowEvaluator`.  Register one carries the assignment's context code through
both balanced maps, so no stage rebuilds the table.
-/

namespace NearCubicWires.CanonicalStructuralGF2EvaluationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedTraversalParityProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalTaggedParityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierPrinter
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## §1 The two arithmetic identities behind the machine -/

/-! ## §2 The fixed zero test

One four-instruction program serves both Boolean roles the evaluator needs:
complementing a variable bit, and turning the balanced sum of complemented
bits into the monomial's conjunction. -/

/-! ## §3 One variable of one monomial

The link-time assignment program is the only semantic parameter of the whole
machine.  Its output is complemented here so that a monomial's conjunction
becomes the zero test of a plain natural sum. -/

/-! ## §5 The complete structural polynomial

The polynomial is the balanced list of its monomial codes.  The same request
tree distributes the assignment context over the monomials, and the fixed
balanced parity fold reduces their bits in characteristic two. -/

/-! ## §6 The canonical finite Boolean assignment

Every structural row polynomial in `CanonicalFourfoldRowProgram` is evaluated
at `encodedFiniteBooleanAssignment`, whose out-of-range convention is `false`
rather than a truncation.  The context code carries the population beside the
balanced table of bits, so the range guard reads its bound from the same word
the table came in, and the fixed balanced lookup does the rest. -/

/-! ## §7 The assignment program

Out-of-range codes are `false` by definition of `encodedFiniteBooleanAssignment`
and by the machine's second branch; no truncation or wrap-around is possible. -/

/-! ## §8 The closed evaluator

Composing §5 with §7 leaves no program parameter: one fixed oracle-free
machine evaluates any structural polynomial against any finite Boolean
assignment table, with closed width and fuel envelopes. -/

/-! ## §9 The symmetric canonical row body

`CanonicalFourfoldRowProgram` already proves that the symmetric row is the
structural polynomial evaluated at the shared residual assignment.  Composing
that identification with §8 executes the row body itself: the machine consumes
only the residual table and the row polynomial, and no stage re-derives the
occurrence pool, the live set, or the circuit masks. -/

/-! ## §10 The row evaluator around one link-time row-data producer

The evaluator's ABI is the row handoff.  Exactly one link-time program
remains: the producer that turns that handoff into the pair
`(assignment context, encoded row polynomial)`.  Everything after it — the
context switch into the closed evaluator of §8 and the evaluation itself — is
executed here with closed width and fuel envelopes. -/

/-! ## §11 The symmetric row evaluator in the published shape

This is the `hevaluator` premise of `run_fourfoldRowModeDispatchProgram_
symmetric` with one remaining link-time obligation: the row-data producer on
the row handoff. -/

/-! ## §12 Splitting the row data into two independent producers

The two halves of the row data — the residual assignment table and the row
polynomial — are read from the same handoff and are otherwise unrelated.  The
verified fork runs both on that one handoff and emits exactly the pair the
native call of §10 consumes. -/

/-! ## §13 The published row evaluators over two producers

Everything below the two producers is now compiled: these are the
`hevaluator` premises of `run_fourfoldRowModeDispatchProgram_symmetric` and
`run_fourfoldRowModeDispatchProgram_threshold` with exactly two remaining
link-time obligations per family. -/

/-! ## §14 The threshold twin

The threshold family differs only in its occurrence pool, its mixed-radix
sample, and its residual offsets; the evaluator and both closures above are
family-neutral. -/

/-! ## §15 Malformed row indices

Row indices outside the finite seed space evaluate to `false` rather than
wrapping.  The evaluator reproduces that convention exactly: the producer
emits the zero polynomial and the machine's parity fold is empty, so no
partiality or truncation is introduced at the boundary. -/

end NearCubicWires.CanonicalStructuralGF2EvaluationProgram
