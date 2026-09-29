import Proof.Circuits.ValidatorCircuitStageWidths

/-!
# The tagged spine's width ledger

`ValidatorCircuitStageWidths` §3 left the Boolean circuit validator with exactly
two fuel charges, and named the single missing ledger each of them needs.  The
first — `booleanCircuitPreparationFuel`, through the node batch and the node
validator, down to `taggedListValidationFuel` — needs a fact that exists nowhere
in the tree:

> a `Nat.unpair` projection is **half** as wide as the code it is taken from.

`ValidatorLeafWidthCore` §6 proves the pairing side of this
(`two_mul_natBitLength_max_le_natBitLength_pair`: a pairing at least *doubles*
the width) and spends it on the structural parse's height.  The projection side
is the same fact read through `Nat.pair_unpair`, and it is what every
`Nat.unpair`-recursive charge in the tagged cone is paid from.  §1 states it as
a standalone ledger, in both projections and in both the coarse (monotone) and
the sharp (halving) form.

* §1 the `Nat.unpair` width ledger.

* §2 spends it on `taggedListValidationFuel`, the tagged spine's structural
  walk: its recursion peels **two** pairings per step, so the width drops by a
  factor of four and the whole walk is *width-linear* — in fact logarithmic, but
  linear is what the domination algebra consumes.

* §3 supplies the matching *counting* ledger for the tagged codec, which nothing
  in the tree published either: a decoded tagged record has at most
  `natBitLength code − 1` fields, and every one of them is no wider than the
  code.  These are the two facts the batch's counted call over
  `taggedNatFieldCodes` is charged against — the exact analogue, for the tagged
  codec, of what `ValidatorLeafWidthCore` §2 and §4 are for the balanced one.
-/

namespace NearCubicWires.ValidatorTaggedSpineLedger

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTaggedListValidationProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ValidatorLeafWidthCore

/-! ## §1 The `Nat.unpair` width ledger

`Nat.pair_unpair` turns `ValidatorLeafWidthCore` §6's pairing rule into a
statement about the projections: since the pairing of the two halves *is* the
code, each half is at most half as wide, up to the one bit the rule loses. -/

/-! ## §2 The tagged spine's structural walk

`taggedListValidationFuel` recurses on `code ↦ (Nat.unpair (Nat.unpair code).2).2`
and charges seven per cell.  Two projections per step means a factor of four in
the width per step, so the depth is logarithmic and the charge is well inside
width-linear.  The only delicate point is the shortest cell: a code whose tag
projection is `1` is at least `2`, so its width is at least `2`, and that is
what keeps the very first step inside the budget. -/

/-! ## §3 The tagged codec's counting ledger

The balanced codec has both halves of its ledger published — the decoded list's
length (`ValidatorLeafWidthCore` §2) and the decoded atoms' widths (§4).  The
tagged codec has neither.  Both follow from the same two facts as §2: a cell is
a pairing of the payload with the tail, and `decodeTaggedList` only accepts
codes it re-encodes exactly. -/

/-! ### At the validator's own field decoder -/

end NearCubicWires.ValidatorTaggedSpineLedger
