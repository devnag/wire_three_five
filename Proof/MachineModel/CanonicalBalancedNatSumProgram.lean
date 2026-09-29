import Proof.Circuits.CanonicalBalancedTraversal

namespace NearCubicWires.CanonicalBalancedNatSumProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

/-! ## Composition boundary

Keep the producer abstract while proving the standard producer-to-sum link.
Concrete producers can be large generated controllers; specializing this opaque
theorem avoids normalizing their instruction layout in every downstream proof.
-/

end NearCubicWires.CanonicalBalancedNatSumProgram
