import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBalancedMidpointRebuildProgram
import Proof.MachineModel.CanonicalBooleanNodeListValidationProgram

/-!
# The node-list validator, rebuilt on the indexed canonicalizer

`CanonicalBooleanNodeListValidationProgram.booleanNodeListValidationProgram`
links seven stages, and the **first** one carries the same geometric charge
`ValidatorCanonicalizerRebuildLedger` repaired for the canonical natural
validator — twice over, once through each arm of a fork:

* the fork's second arm is `balancedRawCanonicalizeProgram` itself, so its
  charge is `balancedRawCanonicalizeBits`, which
  `ValidatorTaggedIntermediateVerdict.two_pow_atoms_le_balancedRawCanonicalizeBits`
  floors at `2 ^ atoms.length`;

* the fork's **first** arm is `balancedCanonicalityProgram`, whose preparation
  stage runs `balancedRawCanonicalizeProgram` under `preserveRightProgram`.  So
  the canonicality guard carries the *same* floor.

`CanonicalBalancedMidpointRebuildProgram.balancedRawCanonicalizeFoldProgram`
replaces that program at an unchanged output contract, so both arms swap at
once.  This module performs the swap and re-assembles the public node-list
validator at its published output.

* §1 the canonicality guard, rebuilt.

* §2 the normalization fork, rebuilt.

* §3 the node-list validator, rebuilt.
-/

namespace NearCubicWires.CanonicalBooleanNodeListRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedMidpointRebuildProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 The canonicality guard, rebuilt -/

/-! ## §2 The normalization fork, rebuilt -/

/-! ## §3 The node-list validator, rebuilt -/

end NearCubicWires.CanonicalBooleanNodeListRebuildProgram
