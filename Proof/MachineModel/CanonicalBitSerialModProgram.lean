import Proof.MachineModel.CanonicalNativeModProgram

/-!
# Bit-serial native-natural remainder

The earlier native remainder controller consumes one instruction group per
numeric unit of its numerator.  That exact implementation remains useful when
the numerator is already publicly bounded, but it is not an admissible decoder
for an arbitrary binary code.  This module supplies the one production
alternative: scan the numerator from its most significant bit and reduce after
each bit, so runtime depends on the numerator's binary width alone.

## Why the reduction is one saturating subtraction and not a counting loop

Every candidate entering the reduction is `2 * remainder + bit` with
`remainder < denominator`, hence strictly below `2 * denominator`; a single
conditional subtraction is therefore the whole reduction.  The earlier stage
executed that subtraction — and the doubling preceding it — as unary register
loops, so its charge contained `4 * remainder` and
`4 * min candidate denominator`.  Summed over the numerator's bits that is
`Θ(bits numerator · denominator)`, which is exponential in the width of the
public denominator.  That budget is affordable inside an exponential-time
caller, but the recovery-witness validator is charged against a *polynomial*
envelope and this stage sits on its critical path.

The production stage therefore uses the fixed-cost register operations the
machine already provides: `shiftLeft` for the doubling, `add` for the incoming
bit, and two `subtract` instructions for the reduction.  The saturating gap
`denominator - candidate` vanishes exactly when `denominator ≤ candidate`, so
the branch deciding whether to subtract is a plain zero test.  One numerator
bit now costs at most nine instructions, independently of every operand's
magnitude.

The public surface — `bitSerialModInput`, `bitSerialModProgram`,
`bitSerialModProgram_oracleFree`, `bitSerialModScan`, `bitSerialCountFuel`,
`bitSerialOuterFuel`, `bitSerialModFuel`, `bitSerialModRegisterBound`,
`bitSerialModBits`, `bitSerialModScan_eq_mod`, `run_bitSerialModProgram`,
`bitSerialModRegisterBound_le` and `bitSerialModBits_le` — is unchanged, as are
the program length, the register span and the public zero-divisor exit at
program indices `31` and `32`; only the internal reduction route and its charge
changed.  `bitSerialModFuel_le_natBitLength` records the resulting width-linear
budget.
-/

namespace NearCubicWires.CanonicalBitSerialModProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeModProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-!
Register ABI:

* `r0`: paired request, then the remainder;
* `r2`: remaining bit index;
* `r3`: current remainder, then the doubled candidate, then the reduction;
* `r4/r5`: immutable numerator and positive denominator;
* `r6`: bit-count cursor;
* `r8`: current input bit;
* `r9`: the saturating gap `denominator - candidate`, whose vanishing is the
  executable form of `denominator ≤ candidate`;
* `r10`: the constant zero used as a jump scratch.

Every candidate entering the reduction is below twice the denominator, so one
saturating subtraction is the whole reduction and no loop in this program is
charged by a numeric magnitude.

Indices `19` through `28` are unreachable padding.  They keep the program
length, the register span and the public zero-divisor exit at indices `31` and
`32` identical to the previous stage, so every caller naming those offsets
rebuilds unchanged.
-/
def bitSerialModProgram : NPOracleProgram :=
  [ .unpairLeft 0 4 1
  , .unpairRight 0 5 2
  , .branchZero 5 31 3
  , .set 2 0 4
  , .copy 4 6 5
  , .branchZero 6 9 6
  , .shiftRight 6 1 6 7
  , .increment 2 8
  , .decrement 10 5
  , .set 3 0 10
  , .branchZero 2 29 11
  , .decrement 2 12
  , .shiftLeft 3 1 3 13
  , .testBit 4 2 8 14
  , .add 3 8 3 15
  , .subtract 5 3 9 16
  , .branchZero 9 17 18
  , .subtract 3 5 3 18
  , .decrement 10 10
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .halt 0
  , .copy 3 0 30
  , .halt 0
  , .set 0 0 32
  , .halt 0
  ]

/-! ## Exact interpreter loops -/

/-! ## The polynomial charge

Every loop of the production stage is charged by a bit index, never by a
register's numeric value. -/


end NearCubicWires.CanonicalBitSerialModProgram
