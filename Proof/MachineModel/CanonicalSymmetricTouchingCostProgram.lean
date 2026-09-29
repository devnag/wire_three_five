import Proof.MachineModel.CanonicalSymmetricSupportMaskProgram

/-!
# The symmetric occurrence pool's touching cost, executed from the envelope

This module closes `CanonicalOccurrencePopulationProgram` §6.  Every ingredient
is already compiled:

* `CanonicalSymmetricSupportMaskProgram` turns the typed envelope into the
  pool's `coordinateMask` list;
* `CanonicalTouchingSweepRoundProgram.run_touchingSweepSelectProgram` runs the
  whole greedy conditional-expectation sweep on that list;
* `CanonicalTouchingSweepRoundProgram.run_roundBroadcast` builds one census
  request tree from a selection mask;
* `CanonicalConditionalTouchProgram.run_touchingCostProgram` scores it at step
  budget zero, which is the touching cost itself.

What is left is the sweep's *live count*.  It is
`min q (liveScale * Nat.clog 2 (q + 2))`, so the canonical ceiling logarithm and
the canonical bit-serial multiplication compute it from the preserved input
length alone; the saturating double subtraction `q - (q - x)` is the minimum.

The sweep's reachable carried states are bounded by one closed numeral: a
carried state is `pair context (pair mask stepCount)` with `mask < 2 ^ q` and
`stepCount ≤ liveCount`, so all four of the sweep controller's width premises
follow from a single envelope.  Only the round callee's own width premise stays
quantified, because it depends on the round's selection set through the census
trees.
-/

open Finset

namespace NearCubicWires.CanonicalSymmetricTouchingCostProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalFourfoldRowCountFormula
open NearCubicWires.CanonicalFourfoldRowCountProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalRowCountExponentProgram
open NearCubicWires.CanonicalSymmetricRowCountReduction
open NearCubicWires.CanonicalSymmetricSupportMaskProgram
open NearCubicWires.CanonicalTouchingSweepProgram
open NearCubicWires.CanonicalTouchingSweepRoundProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

/-! ## §1 Three fixed arithmetic stages -/

/-! ## §2 The sweep's live count -/

/-! ## §3 The sweep's two framing stages -/

/-! ## §4 The sweep's reachable states, in one closed envelope -/

/-! ## §5 The touching-cost program -/

/-! ## §6 The symmetric counting side, closed

`CanonicalOccurrencePopulationProgram` §5 leaves the whole symmetric counting
path waiting on one program returning `symmetricOccurrenceTouchingCost`.  §5 of
this file supplies it, so both consumers become executable. -/

/-! ## §7 The single remaining counting obligation

Every theorem above is unconditional in the counting side's control flow: the
support masks, the live budget, the greedy sweep, the census broadcast, and the
final score are all fixed oracle-free programs, and the sweep controller's four
reachability-indexed width premises are discharged from the closed envelope of
§4.  What is left is a *register-width* premise only, namely the round callee's
own budget on the sweep's reachable rounds:

```text
∀ (selected : Finset (Fin request.q)) (stepCount counter : ℕ),
  counter + 1 ≤ request.q →
  stepCount ≤ normalizedLiveCount request.q liveScale →
  touchingSweepRoundBits (symmetricFourfoldOccurrences request) selected
      stepCount (request.q - (counter + 1)) counter ≤
    costBits
```

Discharging it needs a uniform bound on
`CanonicalTouchingSweepRoundProgram.touchingSweepRoundStageBits` over every
selection set, i.e. a monotone envelope for the two per-round census request
trees; no semantic obligation and no interpreter premise remains. -/

end NearCubicWires.CanonicalSymmetricTouchingCostProgram
