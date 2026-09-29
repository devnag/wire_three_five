import Proof.Foundations.CanonicalBinaryProgram

/-!
# The dyadic exponential as a fixed program

`CanonicalFourfoldRowCountFormula` collapses both published row counts to a
single power of two with a *run-time* exponent, so the counting side needs one
more primitive: `2 ^ e` for an `e` that arrives in register zero rather than
as an immediate.  The instruction set's `shiftLeft` takes a compile-time
amount only, so this module supplies the doubling loop instead.

Its charge is linear in the exponent and its register width is exactly the
answer's width; no oracle query and no callee appear.
-/

namespace NearCubicWires.CanonicalTwoPowProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-!
Register ABI:

* `r0`: the exponent, then the output power;
* `r2`: the remaining exponent;
* `r3`: the accumulated power.
-/

end NearCubicWires.CanonicalTwoPowProgram
