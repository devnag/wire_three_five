import Proof.Foundations.CanonicalBinaryProgram
import Proof.Circuits.RegisterBounds

/-!
# Fixed tagged-stream to canonical-balanced builder

Executable compilers often emit a private forward tagged stream because a
single cons cell is convenient while the stream is being produced.  Public
variable-length values use `encodeBalancedList` so their binary width is
polynomial.  This fixed oracle-free machine is the sole conversion boundary:
it counts the stream, performs the canonical midpoint recursion with an
explicit continuation stack, and returns exactly the balanced encoding.
-/

namespace NearCubicWires.CanonicalBalancedBuilder

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-! Register ABI:

* `r0`: tagged input cursor, then the unconsumed suffix;
* `r1`: current subtree leaf count;
* `r2`: private continuation stack;
* `r3`: completed subtree code and final output;
* `r4`--`r6`: frame and pairing scratch;
* `r7`, `r9`, `r10`: constants zero, one, and two;
* `r8`: saved start of the tagged stream.

A pending frame is `pair rightCount leftCode`; `leftCode = 0` means that the
left subtree is being evaluated.  Every real nonempty subtree code is
positive, so the marker is unambiguous without a second control format. -/

/-! ## Exact tagged-stream counting phase -/

/-! ## Canonical midpoint build phase -/

end NearCubicWires.CanonicalBalancedBuilder
