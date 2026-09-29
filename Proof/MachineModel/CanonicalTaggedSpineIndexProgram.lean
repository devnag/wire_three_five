import Proof.Foundations.CanonicalBinaryProgram

/-!
# Indexed access to one tagged spine

`CanonicalBalancedBuilder.taggedToBalancedProgram` is the tree's only route from
a tagged field list to the balanced ABI, and its published charge
`taggedToBalancedRegisterBitsFor` is `natBitLength` of a `pairIter` clock at the
builder's own fuel.  `ValidatorWidthCombinatorLedger.natBitLength_pairIter_le`
puts that at `2 ^ (42 · fields.length + 14) ·` the input width, and the tagged
codec's own counting ledger only gives `2 ^ fields.length ≤ natBitLength code`,
so the frozen conversion sits at degree `43` over the record's width.  It cannot
be re-charged: the builder's run theorem carries the clock inside its induction
invariant.

`CanonicalBalancedMidpointRebuildProgram` solved the same problem for the
*balanced* codec by replacing the builder with **count, generate one request per
index, then select**.  This module supplies the two tagged-codec leaves that
route needs, at charges that are `natBitLength` of values the machine
demonstrably holds:

* §1 the spine's structural length and lookup, as total functions;

* §2 `taggedSpineLengthProgram` — one five-instruction cell loop, returning the
  field count paired with the code it counted, which is exactly
  `GeneratedBalancedRangeProgram.generatedBalancedRangeInput`;

* §3 `taggedSpineSelectProgram` — the same cell loop counted down by an index,
  returning the selected field, at the request ABI a balanced call hands its
  callee (`inputLength` is the index, register zero is the code).

Neither charge is a clock.  `taggedSpineLengthBits` is the width of the returned
pair and `taggedSpineSelectBits` is the width of the code and the index, so both
are linear in the record's own width.
-/

namespace NearCubicWires.CanonicalTaggedSpineIndexProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock

/-! ## §1 The spine's structural length and lookup -/

/-! ## §2 The spine counter

Register ABI: `r0` holds the code throughout and the returned pair at the end,
`r2` is the cursor, `r3` is the accumulated count and `r4` is the peeled cell.
-/

/-! ## §3 The spine selector

Register ABI: `r0` is the cursor and then the result, `r2` is the index
countdown, `r3` is the peeled cell.  The entry state is the one a balanced call
hands its callee: the request's left component is the public length and its
right component is register zero.
-/

end NearCubicWires.CanonicalTaggedSpineIndexProgram
