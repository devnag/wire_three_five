import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed tagged program choice

`taggedProgramChoice first second` consumes `pair(tag, payload)`, runs `first`
when `tag = 0`, and runs `second` otherwise.  Both branches share one isolated
handoff register and one return halt, so callers do not need parallel wrapper
implementations for heterogeneous balanced calls.
-/

namespace NearCubicWires.TaggedProgramChoice

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

end NearCubicWires.TaggedProgramChoice
