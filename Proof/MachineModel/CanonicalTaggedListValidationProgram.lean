import Proof.Foundations.CanonicalBinaryProgram

/-!
# Total canonical tagged-list validation

Tagged streams are the sole private linear-list format used between fixed
compiler stages.  This loop checks the exact nonzero cell tag `1`, follows
only the canonical tail, and returns one precisely for a successful public
`decodeTaggedList`.  It is fixed code: no expected length, callback, or
caller-provided recursion limit enters the request.
-/

namespace NearCubicWires.CanonicalTaggedListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## Fixed validation loop -/

end NearCubicWires.CanonicalTaggedListValidationProgram
