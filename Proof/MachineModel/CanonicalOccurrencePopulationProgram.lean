import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalRowCountExponentProgram

/-!
# The symmetric occurrence population, executed from the typed envelope

`CanonicalRowCountExponentProgram` leaves the symmetric counting side with two
link-time premises about the occurrence pool.  This module discharges the first
of them.

The symmetric occurrence pool is the concatenation of the bottom fans of the
request's circuits, so its population is the sum of the circuits' bottom counts.
Each bottom count is the *second* field of the circuit's canonical tagged-list
encoding, so the whole quantity is one balanced map followed by the existing
balanced natural-number sum: no circuit is decoded beyond its header, and no
semantic parser is introduced.

After this module the only counting residual left is the touching cost of the
pool.
-/

namespace NearCubicWires.CanonicalOccurrencePopulationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## §1 Three fixed structural stages -/

/-! ## §2 The per-circuit bottom counter -/

/-! ## §3 The balanced bottom-count map -/

/-! ## §4 The symmetric occurrence population -/

/-! ## §5 The counting side, closed to the touching cost

Instantiating the population half of the row-count exponent leaves exactly one
open interpreter premise on the whole symmetric counting path. -/

/-! ## §6 The single remaining counting obligation

Every theorem above is unconditional except for one interpreter premise.  The
exact statement an owning module must supply is

```text
theorem run_symmetricOccurrenceTouchingCostProgram
    (liveScale : ℕ)
    (request : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (maximumBits : ℕ)
    (hbits : symmetricOccurrenceTouchingCostBits liveScale request ≤
      maximumBits) :
    runNPOracleProgram symmetricOccurrenceTouchingCostProgram maximumBits
        (symmetricOccurrenceTouchingCostFuel liveScale request)
        (initialNPOracleState request.q (symmetricEnvelopeCode request)) =
      some (symmetricOccurrenceTouchingCost request liveScale)
```

with `symmetricOccurrenceTouchingCostProgram` oracle-free.  Semantically that
number is

```text
touchingCost (occurrenceSupport occurrences)
  (touchingSelect (occurrenceSupport occurrences)
    (normalizedLiveCount request.q liveScale))
```

for `occurrences = symmetricFourfoldOccurrences request`, i.e. one greedy
conditional-expectation sweep over `List.finRange request.q` in which each step
compares two `conditionalTouchNumerator` scores after cross-multiplying by their
binomial fiber sizes.  Executing it needs an exact `Nat.choose` stage; nothing
else in this file's chain remains open. -/

end NearCubicWires.CanonicalOccurrencePopulationProgram
