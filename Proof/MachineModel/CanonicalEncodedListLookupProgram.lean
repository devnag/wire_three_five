import Proof.MachineModel.PreserveRightProgram

/-!
# Fixed lookup in Lean's canonical `Encodable` list spine

Projection decision runners return `Encodable` codes for lists of three-literal
clauses.  The list instance is the zero/successor pairing spine, so one small
fixed program suffices for both the outer clause lookup and each inner literal
lookup.  This module keeps that codec boundary executable instead of decoding
runner output in the host logic.
-/

namespace NearCubicWires.CanonicalEncodedListLookupProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Reused two-level lookup -/

end NearCubicWires.CanonicalEncodedListLookupProgram
