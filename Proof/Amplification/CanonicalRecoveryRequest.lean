import Proof.MachineModel.CanonicalRecoveryProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Raw weak-request extraction for recovery validation

The verifier receives only `WeakVerifierRequest.code` in register zero.  This
module proves the fixed extraction/linking path that recovers both public input
and witness bits, validates the witness, and preserves the same public input
for the downstream verifier.  No shallow request-level specialization is
retained.
-/

namespace NearCubicWires.CanonicalRecoveryRequest

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker
open scoped BigOperators

/-! ## Input-preserving validator ABI -/

end NearCubicWires.CanonicalRecoveryRequest
