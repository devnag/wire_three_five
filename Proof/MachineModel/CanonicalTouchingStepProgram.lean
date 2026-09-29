import Proof.MachineModel.CanonicalBinomialProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.Supplier.SupplierTouching

/-!
# The touching sweep's per-step comparison, executed

`SupplierTouching.touchingSelectAux` branches on exactly one inequality:

```text
included * Nat.choose rest.length stepCount ≤
  excluded * Nat.choose rest.length (stepCount - 1)
```

where `included` and `excluded` are the two conditional touch numerators of the
current coordinate.  This module turns that branch test into one fixed
oracle-free program with an exact width and clock.

The stage is assembled entirely from verified pieces: a straight-line fan-out
that duplicates the shared `(rest.length, stepCount)` context and takes the
saturating predecessor of the step count, one `CanonicalPairedCall` over a
score program that composes `binomialProgram` with `bitSerialMulProgram`, and a
three-instruction saturating comparison.  No arithmetic is repeated in the
proof: the two binomial coefficients come from `run_binomialProgram` and the
two products from `run_bitSerialMulProgram`.
-/

namespace NearCubicWires.CanonicalTouchingStepProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBinomialProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 One weighted score

`touchingScoreProgram` maps `Nat.pair value (Nat.pair count position)` to
`Nat.choose count position * value`. -/

/-! ## §2 The straight-line fan-out -/

/-! ## §3 The saturating comparison -/

/-! ## §4 The assembled step -/

/-! ## §5 One gate's conditional touch count

`SupplierTouching.conditionalGateTouchCount` is the only per-gate quantity the
sweep ever sums.  Given the gate's meeting indicator and the two fiber
cardinalities it is a difference of two binomial coefficients, so it is one
paired binomial call followed by a saturating selector. -/

end NearCubicWires.CanonicalTouchingStepProgram
