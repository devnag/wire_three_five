import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed length of Lean's canonical encoded list spine

Decision formulas arrive as arbitrary natural codes for `List (List ℕ)`.
Before a structural emitter can enumerate their clauses, it needs the exact
decoded outer-list length.  This fixed fold follows the same successor/pairing
spine as `Encodable.decode`; no decoded host list crosses the machine boundary.
-/

namespace NearCubicWires.CanonicalEncodedListLengthProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

end NearCubicWires.CanonicalEncodedListLengthProgram
