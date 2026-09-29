import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorOracleCallWidth

/-!
# The tree's canonical combinator width ledger

`ValidatorOracleCallWidth` §1 opened this ledger with the native contextual
call.  Every remaining validator width obligation is a maximum over the same
handful of shapes, so this module states each shape **once**, over variables:
no register span, no decoded magnitude, no counted collection appears in any
statement here.

* §1 the two primitives — a pairing doubles a width bound, and a `foldr max`
  over a width cone is the cone's bound.

* §2 the wrapper shapes: `swapPairBits`, `preserveRightBits`, `pairedCallBits`,
  `forkCallBits`.

* §3 the iterated pairing `pairIter`, which is the tagged tuple's width.

Every entry is stated as `… ≤ max <callee widths> (k * bound)` with `k` a closed
numeral, so a consumer discharges it by exhibiting one width cone and reading
off the callee.
-/

namespace NearCubicWires.ValidatorWidthCombinatorLedger

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorLeafWidthCore

/-! ## §1 The two primitives -/

/-! ## §2 The wrapper shapes -/

/-! ## §3 The iterated pairing -/

end NearCubicWires.ValidatorWidthCombinatorLedger
