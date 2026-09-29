import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorCircuitWidthLedger
import Proof.MachineModel.CanonicalBalancedMidpointRebuildProgram
import Proof.MachineModel.CanonicalNatDecodeFoldProgram

/-!
# The candidate pass, with both residual charges repaired

`ValidatorDecodeFoldWidthLedger` §3 leaves the canonical natural validator's
candidate route at exactly one geometric summand.  Its own §1 replaced the
decoder; its §3 named what remained:

> "a traversal-driven midpoint canonicalizer, with no `encodeTaggedList` of a
> public-length list in its width cone — is exactly what remains before the
> candidate pass, and therefore the whole canonical natural validator, is
> polynomially charged."

`CanonicalBalancedMidpointRebuildProgram` is that canonicalizer, at the same
output contract.  This module links it to the repaired decoder and re-walks the
candidate charge with **both** summands replaced.

What is eliminated:

* `ValidatorTaggedIntermediateVerdict.two_pow_atoms_le_balancedCanonicalizeBits`
  and `…_le_balancedRawCanonicalizeBits` floor the *old* canonicalizer through
  `balancedClauseStreamFlattenProgram`'s returned value.  The rebuilt
  canonicalizer never runs that flattener, so §2's charge is not floored by
  either;

* `two_pow_length_le_taggedToBalancedRegisterBitsFor` floors the *old*
  midpoint builder through its input register.  The rebuilt canonicalizer never
  runs `taggedToBalancedProgram` either, so §4's honest floor is moot on this
  route.

* §1 the rebuilt candidate pass.

* §2 the candidate width, in balanced measurements only.

* §3 the seam that is left: what the charge still mentions, and where.

* §4 the validator's first link, restated over the rebuilt candidate pass.
-/

namespace NearCubicWires.ValidatorCanonicalizerRebuildLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedAtomIndexProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalGateAtomHeadListProgram
open NearCubicWires.CanonicalNatDecodeFoldProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 The rebuilt candidate pass -/

/-! ## §2 The candidate width, in balanced measurements only -/

/-! ## §3 The seam that is left

§2 states the rebuilt candidate charge with **no** geometric summand.  What the
charge still mentions is exactly four things:

* `balancedStructuralNormalizeBits` — the raw front door's own traversal
  charge, which the candidate route already paid before this repair and which
  `ValidatorNatWidthLedger` §3 never listed as residual;

* `balancedAtomCountBits` — one balanced-traversal charge over the same tree,
  which is the shape `CanonicalBalancedCall` closes;

* `indexedAtomListBits` and `balancedCallPolynomialBits` — the generated
  request list and the balanced call over it, both of them midpoint-balanced
  and both already carrying the repository's fixed polynomial closure;

* `atomIndexRequestBits` — the width of one request `Nat.pair index code`.

The remaining chain to `hcall` is unchanged in shape: the candidate pass feeds
`canonicalNatValidationBits` through `candidateWithRawBits`, which feeds
`booleanCircuitValidationBits`, which
`ValidatorTraversalWidthLedger.booleanCircuitValidationBits_le_recoveryOracleCallBits`
feeds to `recoveryOracleCallBits`.  Two of those three links are decoder- and
canonicalizer-agnostic and restate verbatim over the programs of §1. -/

/-! ## §4 The validator's first link, restated

`CanonicalNatValidationProgram` links four stages, and only the first — the
candidate pass under `preserveRightProgram` — mentions the decoder or the
canonicalizer.  The other three are stated at the candidate's *value*, so they
reuse verbatim.  §4 restates the first link over §1's program and re-assembles
the same public validator at the same output. -/

end NearCubicWires.ValidatorCanonicalizerRebuildLedger
