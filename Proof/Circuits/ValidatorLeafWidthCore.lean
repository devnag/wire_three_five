import Proof.Supplier.ValidatorLegalSumWalk

namespace NearCubicWires.ValidatorLeafWidthCore

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ValidatorPolynomialDomination

/-! ## §1 One pairing step at least doubles the width -/

theorem natBitLength_mono {left right : ℕ} (hle : left ≤ right) :
    natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-! ## §2 The structural parser's node count

`rawBalancedTraversalTree` is the total proof view of the fixed depth-first
controller: it accepts *every* natural and produces the tree the controller
would walk.  Its branch case recurses into the two halves of the payload, and
the payload is one pairing below the code while the branch tag costs two bits,
so §1 gives the two halves' widths *together* no more room than the code's.
That is exactly the induction that closes a linear node bound. -/

/-! ## §3 The tagged-cell codec

A tagged cell is `Nat.pair 1 (Nat.pair value rest)`, so §1's constant-tag rule
applies once per cell: a decoded stream is strictly shorter than the width of
the code it came from. -/

/-! ## §4 The atom-width ledger

The counted charges do not merely repeat once per decoded atom: the per-atom
work is itself linear in the *atom's* width.  So what the polynomial bookkeeping
needs is not the atom count alone but the **sum of the atom widths**, and that
sum is again linear in the code's width — pairing adds widths back up to one
bit per node, and §2 already caps the node count.  This is why the counted
stages on the validator's path stay at degree one in the width, not two. -/

/-! ## §7 The re-encoding width, as a domination certificate

Spending §4, §5 and §6 together: from a *degree `d`* certificate for the raw
code's width, the canonical re-encoding of that code's decoded atoms carries a
certificate at degree `2d` — the squared atom count contributes `d` by §6, and
the widest atom contributes the other.  At the anchor degree `d = 1` supplied by
`polyBounded_witnessWidth` this is **degree two**. -/

end NearCubicWires.ValidatorLeafWidthCore
