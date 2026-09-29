import Proof.Circuits.CanonicalBalancedTraversal
import Proof.Circuits.CallableRelocation

/-!
# Canonical balanced call traversal

This module gives one executable ABI for applying a verified oracle program to
a variable list of requests.  Both requests and outputs use
`encodeBalancedList`; the controller therefore has linear fuel and logarithmic
structural depth instead of materializing a linked-list integer.
-/

namespace NearCubicWires.CanonicalBalancedCall

open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.VerifiedLinker

/-! ## Native-input request framing -/

end NearCubicWires.CanonicalBalancedCall
