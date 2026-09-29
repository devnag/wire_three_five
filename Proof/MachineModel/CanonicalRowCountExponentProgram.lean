import Proof.MachineModel.CanonicalFourfoldListDenominatorProgram
import Proof.MachineModel.CanonicalNatCeilLogProgram
import Proof.Circuits.CanonicalSymmetricRowCountReduction

/-!
# The symmetric row-count exponent, executed from the typed envelope

`CanonicalSymmetricRowCountReduction` collapses the entire symmetric counting
side of the artifact to one natural number,

```text
symmetricRowCountExponent liveScale accuracyExponent request
  = 2 * toeplitzWalkSideBits
        (canonicalGradedRank population touchingCost) +
      320 * Nat.clog 2 (listDenominator + 1)
```

and to one residual program computing it from the typed envelope.  This module
supplies that program *except* for the two request-derived pool quantities.

Every arithmetic stage between those quantities and the exponent is fixed here:
the dyadic scalings `256 *` and `320 *` are single shift instructions, the
graded rank is a maximum of two ceiling logarithms, and the padded Toeplitz walk
side is a shift/add/shift triple.  Nothing in this module decodes a circuit, so
the two residual programs remain the sole open obligations on the counting side:

* one program returning `symmetricOccurrencePopulation request`;
* one program returning `symmetricOccurrenceTouchingCost request liveScale`.

Both are quantified as link-time parameters with exact interpreter premises, in
the same style as the row counter they feed.
-/

namespace NearCubicWires.CanonicalRowCountExponentProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldListDenominatorProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierWalkBridge
open NearCubicWires.VerifiedLinker

/-! ## §1 Two dyadic register identities

The interpreter's shift instructions carry an immediate amount, so every
constant scaling used by the exponent is one instruction. -/

/-! ## §2 The fixed structural stages

Five straight-line adapters and one branch-free maximum.  None of them decodes
a canonical list; they only move machine words between the pair positions used
by `preserveRightProgram`. -/

/-! ## §3 The graded rank and the padded walk side

`canonicalGradedRank` is the maximum of two ceiling logarithms and
`toeplitzWalkSideBits` halves `3 *` its argument, so one branch and three shift
instructions cover both. -/

/-! ## §4 The graded-rank half of the exponent

Nine fixed stages take the typed envelope to `2 * toeplitzWalkSideBits` of the
canonical graded rank.  Two of them are the residual pool programs; the rest are
the adapters of §2, the maximum of §3, and two copies of the existing ceiling
logarithm. -/

/-! ## §5 The denominator half of the exponent

The list denominator already has a fixed program; the exponent adds the
canonical positivity shift, one ceiling logarithm, and the powered-label
scaling `320 = 2 ^ 8 + 2 ^ 6`. -/

/-! ## §6 The assembled exponent

The two halves are computed from the same request word by one duplication and
two count-preserving calls, and added. -/

/-! ## §7 The symmetric row-count exponent

Instantiating both halves at the symmetric family closes every stage of the
counting residual except the two pool quantities. -/

/-! ## §8 The symmetric counting side, closed to the pool quantities

Composing with `CanonicalSymmetricRowCountReduction` removes the exponent
parameter from the published row counter, the row-major atom counter, and the
shared aggregation program.  What remains on the counting side is exactly two
interpreter premises about the occurrence pool. -/

end NearCubicWires.CanonicalRowCountExponentProgram
