import Proof.MachineModel.CanonicalNativeModProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Fixed external-literal decoder

The projection decision runner returns arbitrary natural codes.  Its semantic
interface decodes a literal by unpairing the code, reducing the tag modulo two,
and reducing the index modulo the positive query arity.  This module performs
that same operation with fixed programs, reusing the canonical remainder
machine for the only nontrivial arithmetic step.
-/

namespace NearCubicWires.CanonicalLiteralDecodeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeModProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

end NearCubicWires.CanonicalLiteralDecodeProgram
