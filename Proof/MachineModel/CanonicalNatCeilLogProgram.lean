import Proof.Foundations.CanonicalBinaryProgram

/-!
# The base-two ceiling logarithm as a fixed program

`Nat.clog 2` selects every canonical walk length and graded rank in the
normalized supplier: `canonicalWalkLength denominator` is
`2 * Nat.clog 2 (denominator + 1) + 1`, and `canonicalGradedRank` is a maximum
of two base-two ceiling logarithms.  Consequently no executable row counter
can exist until the machine can evaluate `Nat.clog 2`.

This module supplies that primitive.  The loop compares by saturating
subtraction rather than by an inlined comparator, so the whole program is a
single fixed instruction list with no callee and no oracle query, and its
charged fuel is linear in the answer rather than in the input value.
-/

namespace NearCubicWires.CanonicalNatCeilLogProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-!
Register ABI:

* `r0`: the input value, then the output logarithm;
* `r2`: the current power `2 ^ offset`;
* `r3`: the current exponent `offset`;
* `r4`: the saturating difference `value - 2 ^ offset`, which is zero exactly
  when the loop has reached the ceiling logarithm.
-/

end NearCubicWires.CanonicalNatCeilLogProgram
