import Proof.Foundations.CanonicalBinaryProgram

/-!
# Count-preserving program adapter

`preserveRightProgram source` adapts a fixed program from `left ↦ output` to
`pair(left, right) ↦ pair(output, right)`.  It executes `source` exactly once,
keeps the right component outside the source's register span, and proves the
exact fuel and register-width refinement needed by downstream linkers.
-/

namespace NearCubicWires.PreserveRightProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

end NearCubicWires.PreserveRightProgram
