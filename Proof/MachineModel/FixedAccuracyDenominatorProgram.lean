import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed inverse-polynomial accuracy schedule

The accuracy exponent is fixed before the weak machine is chosen.  This file
therefore compiles that exponent into one oracle-free program computing
`q ^ exponent` from the public arity `q`; there is no run-time function,
certificate, or precomputed denominator in the request ABI.
-/

namespace NearCubicWires.FixedAccuracyDenominatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

end NearCubicWires.FixedAccuracyDenominatorProgram
