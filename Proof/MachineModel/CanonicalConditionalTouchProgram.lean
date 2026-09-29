import Proof.MachineModel.CanonicalOccurrencePopulationProgram
import Proof.MachineModel.CanonicalTouchingStepProgram

/-!
# The conditional touch numerator, executed

`SupplierTouching.conditionalTouchNumerator` is the only quantity the greedy
touching sweep ever sums: one closed binomial score per retained occurrence.
`CanonicalTouchingStepProgram.run_gateTouchProgram` already executes a single
gate's score from the *numeric* triple `(meets, undecidedCard, residualCard)`.
This module supplies the missing half — turning coordinate sets into machine
data and folding the per-gate program across the whole occurrence pool.

Coordinate sets travel as bitmasks: `coordinateMask` is the little-endian
`Nat.ofBits` numeral of a `Finset (Fin q)`, so membership is one `testBit`
instruction.  A single counted loop over the `q` coordinate positions then
computes all three per-gate numbers at once, using only saturating arithmetic:

```text
undecidedCard += undecidedBit
residualCard  += undecidedBit - supportBit          -- AND NOT
meets         += selectedBit + supportBit - 1       -- AND
```

Saturating subtraction on single bits is exactly Boolean `AND NOT`, and
`x + y - 1` on single bits is exactly Boolean `AND`, so the loop never
branches on data.  Only `meets = 0` is ever observed, and that happens exactly
when the selected set and the gate's support are disjoint.

The pool-level score is then one canonical balanced call of the per-gate
program followed by the existing balanced natural-number sum.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.CanonicalConditionalTouchProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalTouchingStepProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

/-! ## §1 Coordinate sets as bitmasks -/

/-! ## §2 The three coordinate censuses -/

/-! ## §3 The censuses are the ledger's set quantities -/

/-! ## §4 The fixed census program

Register ABI:

* `r0`: the census request, then the `gateTouchProgram` request it builds;
* `r1`: native input length, never written;
* `r2`, `r3`, `r4`: the selected, undecided, and support masks;
* `r5`: the descending coordinate counter;
* `r6`, `r7`, `r8`: the meets, undecided, and residual accumulators;
* `r9`: the step count, carried through untouched;
* `r10`, `r11`, `r12`: the three extracted coordinate bits;
* `r13`: arithmetic scratch and output plumbing.
-/

/-! ## §5 One occurrence's conditional touch count -/

/-! ## §6 The whole occurrence pool -/

/-! ## §7 Mask arithmetic for the greedy sweep

The sweep updates its two coordinate sets one coordinate at a time, so a
controller carrying bitmasks only ever adds or removes a single power of two.
-/

/-! ## §8 The touching cost and the greedy sweep's step

At `stepCount = 0` the same fold is the touching cost itself
(`SupplierTouching.conditionalTouchNumerator_zero`), so no second program is
needed for the sweep's final answer. -/

end NearCubicWires.CanonicalConditionalTouchProgram
