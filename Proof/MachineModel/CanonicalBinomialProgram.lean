import Proof.Foundations.CanonicalBinaryProgram

/-!
# The exact binomial-coefficient primitive

The symmetric touching-cost sweep compares two conditional expectation scores
after cross-multiplying by binomial fiber sizes, so every executable stage on
that path needs `Nat.choose` as a fixed register-machine program.

The instruction set has no register-amount shift, no multiplication, and no
division, which rules out both the compact "row-as-one-integer" Pascal trick
driven by a variable shift and the multiplicative recurrence
`choose m (k+1) = choose m k * (m-k) / (k+1)`.  This module uses a third route
that needs *only* unit shifts, addition, and saturating subtraction.

Write `width := count + 1` and `base := 2 ^ width`.  Because
`Nat.choose count index ≤ 2 ^ count < base`, the natural number

```text
packedPascalRow count = (base + 1) ^ count
```

is exactly the base-`base` numeral whose digit at position `index` is
`Nat.choose count index`.  The machine builds that numeral by `count`
rounds of `value := value + value * base` — where `value * base` is a loop of
`width` unit left shifts — and then reads digit `position` off by `width *
position` unit right shifts followed by a truncation to the low `width` bits,
which is one round trip through unit shifts and a single subtraction.

Both the packing identity and the digit-extraction identity are proved here
from `add_pow`; nothing is decided numerically and no `Nat.choose` value is
ever tabulated in the proof.
-/

namespace NearCubicWires.CanonicalBinomialProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## §1 The packed Pascal row -/

/-! ## §2 The fixed program

Register ABI:

* `r0`: paired request `Nat.pair count position`, then the output digit;
* `r1`: native input length, never written;
* `r2`: `count`;
* `r3`: `position`;
* `r4`: `binomialWidth count`, immutable after setup;
* `r5`: the packed row, then its shifted remainder;
* `r6`: outer round counter;
* `r7`: unit-shift counter;
* `r8`: shift scratch.
-/

/-! ## §3 The two unit-shift loops -/

/-! ## §4 The two counted outer loops -/

/-! ## §5 Public width, clock, and exact execution -/

end NearCubicWires.CanonicalBinomialProgram
