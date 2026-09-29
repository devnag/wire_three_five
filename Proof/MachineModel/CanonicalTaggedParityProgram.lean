import Proof.MachineModel.CanonicalNatDecodeProgram

/-!
# Canonical parity of a balanced bit stream

Case 2 evaluates one fixed seed program on each consecutive input block and
XORs the resulting bits.  The balanced caller already produces the canonical
balanced output tree.  This module reuses its sole balanced-to-tagged adapter
and adds the smallest possible tagged fold: nonzero entries toggle one Boolean
accumulator.  No decoded list, host parity callback, or second tree traversal
crosses the executable boundary.
-/

namespace NearCubicWires.CanonicalTaggedParityProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-!
Register ABI:

* `r0`: tagged cursor, then output;
* `r2`: Boolean parity accumulator;
* `r4`: current bit;
* `r5`: current tagged-cell payload.

Malformed nonzero bit values intentionally count as `true`, matching every
other Boolean-output boundary in the executable layer.
-/

/-! ## Canonical balanced entry point -/

end NearCubicWires.CanonicalTaggedParityProgram
