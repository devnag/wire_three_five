import Proof.Foundations.CanonicalBinaryProgram

/-!
# Canonical run-time bit slice

`BitInputPrefixProgram` reads the low `width` digits of a code.  The Case-2
occurrence coordinates additionally need an interior window: the clause
address of one occurrence input occupies digits `offset, …, offset + width - 1`
of the public code, and both `offset` and `width` are run-time data recovered
from the scheduled envelope, so the immediate `shiftRight` amount of the
instruction set cannot be used.

This module supplies the single fixed program for that window.  It scans the
selected digits from high to low with the register-indexed `testBit`
instruction and doubles the accumulator with one `add`; no second window
convention, no host-side shift, and no per-width program family is introduced.
-/

namespace NearCubicWires.CanonicalBitSliceProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## 1. The scanned value -/

/-! ## 2. The fixed program -/

/-!
Register ABI:

* `r0`: request, then output;
* `r2`: window offset;
* `r3`: request tail, then the current absolute digit index;
* `r4`: remaining digit count;
* `r5`: scanned value;
* `r6`: accumulator;
* `r7`: current digit.

Instruction `11` is the canonical unconditional jump: both branch targets of
`branchZero` are the loop head.
-/

/-! ## 3. Exact execution -/

end NearCubicWires.CanonicalBitSliceProgram
