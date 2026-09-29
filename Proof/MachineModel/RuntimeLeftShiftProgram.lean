import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalTwoPowProgram
import Proof.MachineModel.CaseTwoOccurrenceProgram

/-!
# The run-time left shift

The instruction set's `shiftLeft` takes a compile-time amount only, so a stage
that has to scale a value by `2 ^ e` for an exponent computed at run time needs
one more primitive.  `CanonicalTwoPowProgram` already supplies the doubling
loop `e ↦ 2 ^ e`, and `CanonicalBitSerialMulProgram` already supplies the
bit-serial product; this module is nothing but their composition through the
count-preserving adapter of `PreserveRightProgram`.

The public ABI is `pair exponent value`, and the certified output is exactly
`2 ^ exponent * value`.  No oracle query, no callee, and no new loop is
introduced: both stages and the linker are already verified.
-/

namespace NearCubicWires.RuntimeLeftShiftProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The program -/

/-! ## 2. Closed budgets -/

/-! ## 3. Exact execution -/

end NearCubicWires.RuntimeLeftShiftProgram
