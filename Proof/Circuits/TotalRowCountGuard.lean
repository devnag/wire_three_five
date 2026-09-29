import Proof.MachineModel.TaggedProgramChoice

/-!
# A reusable zero-count call guard

This is the small ABI adapter used by the total PCP row emitter.  It preserves
the original `pair table (pair count payload)` request, exposes `count` as a
choice tag, and runs a canonical-zero branch before the nonzero callee can
decode the payload.
-/

namespace NearCubicWires.TotalRowCountGuard

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

end NearCubicWires.TotalRowCountGuard
