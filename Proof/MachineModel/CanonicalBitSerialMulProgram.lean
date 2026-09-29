import Proof.Foundations.CanonicalBinaryProgram

/-!
# Bit-serial natural multiplication

This module provides the fixed multiplication primitive used by executable
resource accounting.  It scans the multiplier in binary, so charged fuel is
linear in the multiplier's bit width rather than its numeric value.
-/

namespace NearCubicWires.CanonicalBitSerialMulProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-!
Register ABI:

* `r0`: paired request, then accumulator/output;
* `r2`: current shifted multiplicand;
* `r3`: remaining multiplier;
* `r4`: immutable zero bit index;
* `r5`: current low bit.

The loop preserves `accumulator + multiplicand * remaining = left * right`.
The final redundant copy is intentional: it gives the back edge a dedicated
instruction and keeps every jump target within the fixed program.
-/

end NearCubicWires.CanonicalBitSerialMulProgram
