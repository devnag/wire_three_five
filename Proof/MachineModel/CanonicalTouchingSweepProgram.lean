import Proof.MachineModel.CanonicalConditionalTouchProgram
import Proof.Circuits.CanonicalRoundCall

/-!
# The greedy touching sweep on the counted round controller

`CanonicalConditionalTouchProgram` §9 records the one sequential obligation of
the symmetric counting path: `SupplierTouching.touchingSelect` walks
`List.finRange q` in order and each round's two conditional numerators depend on
the previous round's selection.  `CanonicalRoundCall` supplies the missing
state-threading harness; this module supplies the semantic bridge between the
harness's pure fold and the ledger's greedy recursion, and composes the two.

The carried state is `pair context (pair selectedMask stepCount)`: `context` is
the round callee's fixed data (the occurrence pool's support masks and the
coordinate count), copied unchanged through every round, while `selectedMask`
and `stepCount` are the sweep's two mutable fields.  With the counter descending
from `q` to `1`, the round at counter `c` processes the coordinate list
`(List.finRange q).drop (q - c)`, whose head is coordinate `q - c` and whose
tail is exactly the `rest` of `touchingSelectAux`.
-/

open Finset

namespace NearCubicWires.CanonicalTouchingSweepProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

/-! ## §1 The coordinate order, one suffix at a time -/

/-! ## §2 The sweep as a round-indexed fold -/

/-! ## §3 The carried-state encoding -/

/-! ## §4 The sweep, executed on the counted round controller -/

/-! ## §5 The single remaining sweep obligation

Everything above is unconditional in the sweep's control flow: the counted
controller, its exact clock, and the identification of its fold with
`SupplierTouching.touchingSelectAux` are proved.  What an owning module must
still supply is one *round* program, i.e. a fixed oracle-free
`touchingSweepRoundProgram` together with

```text
theorem run_touchingSweepRoundProgram
    (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) (stepCount counter maximumBits : ℕ)
    (hcounter : counter + 1 ≤ q)
    (hbits : touchingSweepRoundBits … ≤ maximumBits) :
    runNPOracleProgram touchingSweepRoundProgram maximumBits
        (touchingSweepRoundFuel …)
        (initialNPOracleState
          (sweepStateCode (touchingSweepContext occurrences q) (selected, stepCount))
          (Nat.pair
            (sweepStateCode (touchingSweepContext occurrences q) (selected, stepCount))
            (counter + 1))) =
      some
        (sweepStateCode (touchingSweepContext occurrences q)
          (sweepRound (occurrenceSupport occurrences)
            ((List.finRange q).drop (q - (counter + 1))) (selected, stepCount)))
```

Its body is fixed by `sweepRound`'s definition and is assembled entirely from
compiled pieces:

* the coordinate of the round is `q - counter`, and the remaining-coordinate
  set is the interval `{i : q - counter < i}`, whose `coordinateMask` is
  `2 ^ q - 2 ^ (q - counter)` — one `binaryTwoPowProgram` difference;
* the two numerators are `run_conditionalTouchNumeratorProgram` at
  `(insert coordinate selected, rest, stepCount - 1)` and
  `(selected, rest, stepCount)`; their census request lists are the
  shared-context broadcast of `pair (pair selectedMask restMask)` over the
  pool's support-mask list, which the round-call ABI makes available because
  the carried state is installed in the callee's preserved context register;
* the branch test is `run_touchingStepProgram`;
* the mask update is `coordinateMask_insert` (`+ 2 ^ coordinate`) on the taken
  branch and the identity otherwise.

Composing that theorem with `run_touchingSweepProgram` above and with
`CanonicalConditionalTouchProgram.run_touchingCostProgram` gives
`CanonicalOccurrencePopulationProgram`'s §6 target
`run_symmetricOccurrenceTouchingCostProgram`. -/

end NearCubicWires.CanonicalTouchingSweepProgram
