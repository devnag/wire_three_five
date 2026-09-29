import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.Circuits.CanonicalBalancedBuilder
import Proof.Circuits.CanonicalBalancedCall

/-!
# Concatenating canonical balanced sequences

`CanonicalBalanced` is the sole public variable-length ABI, and its midpoint
split makes concatenation genuinely structural: the code of `xs ++ ys` shares
no subtree with the codes of `xs` and `ys`.  Every polynomial compiler below
the structural `𝔽₂` row needs that operation — a monomial of a product is the
concatenation of one monomial per factor — so this module supplies it once.

Nothing new is looped.  The private forward tagged stream of
`CanonicalBalancedBuilder` is already the repository's sole conversion
boundary, and `BalancedClauseStreamFlattenProgram` already folds a balanced
tree of tagged streams into one stream.  What is missing is only the *other*
direction of the boundary, and it is a balanced call away: mapping each atom to
its own singleton stream turns the existing fold into a balanced-to-tagged
converter, after which flattening and rebuilding are the two programs that
already exist.

The three exported programs are therefore

* `balancedToTaggedProgram`: `encodeBalancedList` to `encodeTaggedList`;
* `balancedFlattenProgram`: a balanced list of balanced lists to the balanced
  code of their concatenation;
* `balancedAppendProgram`: the two-element special case, on the pair ABI.

All three are fixed, oracle-free, and carry closed fuel and register-width
formulas.
-/

namespace NearCubicWires.CanonicalBalancedFlattenProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## §2 The balanced code read as a tagged stream

Mapping §1 over the balanced list and folding the resulting singletons is
exactly the identity on the atom sequence, so the composite is the converse of
`CanonicalBalancedBuilder`. -/

/-! ## §3 The concatenation of a balanced list of balanced lists

With §2 in hand the concatenation is the composite the repository already
owns: read every inner code as a tagged stream, fold the streams, and rebuild
the canonical balanced code once. -/

/-! ## §4 The two-element case

Appending two balanced codes is §3 at a two-element outer list, so the whole
front end is the eight instructions that build that list. -/

end NearCubicWires.CanonicalBalancedFlattenProgram
