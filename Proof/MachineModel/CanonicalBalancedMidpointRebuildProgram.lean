import Proof.MachineModel.CanonicalBalancedAtomIndexProgram
import Proof.MachineModel.CanonicalGateAtomHeadListProgram

/-!
# The midpoint canonicalizer, rebuilt by index

`CanonicalBalancedValidationProgram.balancedCanonicalizeProgram` maps every
atom of a structural balanced tree to its own tagged singleton, folds the tree
into one `encodeTaggedList tree.atoms`, and rebuilds the canonical midpoint
code from that stream.  `ValidatorTaggedIntermediateVerdict` §3 shows the
middle step returns a value of width at least `2 ^ tree.atoms.length`, so the
stage's charge is geometric in the *public* atom count at a value the machine
actually produces.  No retuning of `balancedCanonicalizeBits` can repair that;
only a different program can.

This module is that program.  The linked intermediate is replaced by
**indexing**, which needs no cons list at all:

1. `balancedAtomCountProgram` folds the atom count off the shared traversal
   and returns it beside the untouched input code — which is exactly
   `generatedBalancedRangeInput`;

2. `atomRequestListProgram` over the identity stage turns that pair into the
   canonical balanced list of requests `Nat.pair index tree.code`, one per
   atom index.  Every intermediate here is a *midpoint* balanced code, so
   `CanonicalBalancedCall`'s fixed polynomial already covers it;

3. `balancedCallProgram balancedAtomSelectProgram` maps each request to the
   atom at its index.  The balanced-call request ABI hands a callee the
   request's left component as its native input length, which is precisely
   where `balancedAtomSelectProgram` reads its index, and the callee's output
   list is returned as one canonical balanced code.

The composite's output contract is `balancedCanonicalizeProgram`'s own —
`some (encodeBalancedList tree.atoms)` at `initialNPOracleState inputLength
tree.code` — so it is a drop-in replacement and nothing above restates.

* §1 the identity stage and the request family.

* §2 the rebuilt canonicalizer, executed.

* §3 the raw front door, executed.

* §4 the charge, in balanced measurements only.
-/

namespace NearCubicWires.CanonicalBalancedMidpointRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalSignedAtomRequestProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## §1 The identity stage and the request family -/

/-! ## §2 The rebuilt canonicalizer -/

/-! ## §3 The raw front door -/

/-! ## §4 The charge, in balanced measurements only -/

end NearCubicWires.CanonicalBalancedMidpointRebuildProgram
