import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.PreserveRightProgram

/-!
# Canonical single native-input call

Some linked stages compute the input length required by their next callee.
The balanced-call ABI already represents such a request as
`pair(inputLength, requestCode)`.  This module supplies the unique singleton
adapter: wrap that request as a canonical balanced leaf, run the existing
balanced caller, and unwrap its single output.  It introduces no second
relocation or call protocol.
-/

namespace NearCubicWires.CanonicalNativeCallProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed singleton adapters -/

/-! ## One explicit-input call through the balanced ABI -/

/-! ## Explicit-input call with retained context -/

end NearCubicWires.CanonicalNativeCallProgram
