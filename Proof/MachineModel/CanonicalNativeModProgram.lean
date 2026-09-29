import Proof.Foundations.CanonicalBinaryProgram

/-!
# Fixed native-natural remainder

External literal codes use `index % arity`.  This module implements that exact
positive-denominator operation with the existing bounded register machine.
The controller performs explicit chunked subtraction, retaining the current
chunk offset as the remainder; it adds no arithmetic opcode or host callback.
-/

namespace NearCubicWires.CanonicalNativeModProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

end NearCubicWires.CanonicalNativeModProgram
