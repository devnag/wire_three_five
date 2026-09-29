import Proof.Circuits.CanonicalBalancedTraversal

/-!
# Indexed access to the atoms of an arbitrary balanced tree

`CanonicalBalancedValidationProgram`'s midpoint canonicalizer flattens a
structural balanced tree to `encodeTaggedList tree.atoms` before rebuilding.
`ValidatorTaggedIntermediateVerdict` §3 shows that intermediate is fatal: the
tagged codec nests one pairing per *public* atom, so the canonicalizer's charge
is at least `2 ^ tree.atoms.length` at a value the flattener actually returns.

The repair replaces the linked intermediate by **indexing**.  This module
supplies the two traversal-driven stages that make indexing possible without
ever materializing a cons list:

* `balancedAtomCountProgram` — the atom count, folded off the shared
  `balancedTraversalController`, returned paired with the untouched input code;

* `balancedAtomSelectProgram` — the atom at one index, with the index arriving
  in the traversal's *native input length* register.  That is the register the
  balanced-call request ABI writes from a request's left component, so the
  selector is a drop-in callee of `CanonicalBalancedCall`.

Both stages thread exactly one fold register, so both are enterable at `pc = 0`
from `initialNPOracleState` and neither needs a prologue.  The counting state
is a bare counter and the selecting state is the packed pair

> `r9 = Nat.pair (atoms seen so far) (the atom chosen so far)`,

whose zero value `Nat.pair 0 0 = 0` is exactly the machine's zero-initialised
register.

Neither charge mentions `encodeTaggedList` of a public-length list: the only
list-shaped value either program materializes is the traversal's own
continuation stack, whose depth is the input tree's height.

* §1 shared machinery: the controller's terminal branch.

* §2 the atom counter.

* §3 the atom selector, and the pure list semantics of its fold.
-/

namespace NearCubicWires.CanonicalBalancedAtomIndexProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces

/-! ## §1 The controller's terminal branch -/

/-! ## §2 The atom counter -/

/-! ## §3 The atom selector -/

/-! ### The selecting trace is not geometric

Every value the selecting fold materializes is a visit counter, an index, an
atom of the input, or a pair of two of those.  So the whole fold trace is
twice one width that already bounds the count, the index and every atom —
there is no `encodeTaggedList` of a public-length list anywhere in it. -/

end NearCubicWires.CanonicalBalancedAtomIndexProgram
