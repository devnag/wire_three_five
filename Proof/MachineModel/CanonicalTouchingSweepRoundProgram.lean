import Proof.MachineModel.CanonicalTouchingSweepProgram

/-!
# The greedy touching sweep, one round at a time

`CanonicalTouchingSweepProgram` §5 leaves exactly one obligation on the
symmetric counting path: a *round* program whose single step is
`CanonicalTouchingSweepProgram.sweepRound`.  This module supplies it, and
composes it with the counted round controller to obtain the executable
`SupplierTouching.touchingSelect`.

The round's data is fixed by `sweepRound`'s definition:

* the coordinate of the round at descending counter `counter + 1` is
  `q - (counter + 1)`, and the remaining-coordinate set is the suffix
  `(List.finRange q).drop (q - counter)`, whose `coordinateMask` is the
  one-`binaryTwoPowProgram` difference `2 ^ q - 2 ^ (q - counter)`;
* the two conditional numerators are
  `CanonicalConditionalTouchProgram.run_conditionalTouchNumeratorProgram` at
  `(insert coordinate selected, rest, stepCount - 1)` and
  `(selected, rest, stepCount)`, whose census request lists are the
  shared-context broadcast of `pair (pair selectedMask restMask)` over the
  pool's support-mask list;
* the branch test is `CanonicalTouchingStepProgram.run_touchingStepProgram`;
* the mask update is `coordinateMask_insert`, taken through the machine's
  `testBit` so that the update is correct even for a coordinate the carried
  mask already holds.

The round callee's context register `r1` carries the whole sweep state, so the
broadcast reads its shared census fields straight from the round-call ABI.
-/

open Finset

namespace NearCubicWires.CanonicalTouchingSweepRoundProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalConditionalTouchProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalOccurrencePopulationProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalRoundCall
open NearCubicWires.CanonicalTouchingStepProgram
open NearCubicWires.CanonicalTouchingSweepProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierTouching
open NearCubicWires.VerifiedLinker

/-! ## §1 The remaining-coordinate suffix, as a bitmask -/

/-! ## §2 The pool's support masks and the round context -/

/-! ## §3 One census request, built from the shared context -/

/-! ## §4 The shared-context broadcast over the support-mask list -/

/-! ## §5 One numerator's request tree, on a computed context -/

/-! ## §6 Both numerators of one round -/

/-! ## §7 The round's straight-line stages -/

/-! ## §8 The round's greedy comparison -/

/-! ## §9 The round program -/

/-! ## §10 The greedy sweep, executed -/

end NearCubicWires.CanonicalTouchingSweepRoundProgram
