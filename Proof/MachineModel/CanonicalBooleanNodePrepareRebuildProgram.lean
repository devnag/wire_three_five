import Batteries.Tactic.OpenPrivate
import Proof.MachineModel.CanonicalBooleanNodeListRebuildProgram
import Proof.MachineModel.CanonicalTaggedNatListRebuildProgram

/-!
# The preparation fork, rebuilt on the indexed tagged spine

`ValidatorRebuildWidthLedger` §5 isolates `booleanNodeListPrepareBits` as the
single residual stage of the rebuilt node-list validator, and walks it down to

> `booleanCircuitPreparationBits`, which forks a balanced length count against
> `booleanNodeBatchBits` — a counted call that charges
> `booleanNodeValidationBits` once per descriptor, and each of those charges
> `taggedNatListValidationBits`.

`CanonicalTaggedNatListRebuildProgram` replaces the bottom of that chain at an
unchanged output contract.  This module is the frozen linking with the callee
swapped, one stage at a time, exactly as
`CanonicalBooleanNodeListRebuildProgram` did for the normalization fork: every
stage above the swap is stated at the *value* the swapped callee returns, so
each linking proof replays verbatim.

* §1 the node validator, rebuilt.

* §2 the node batch, rebuilt.

* §3 the preparation fork, rebuilt.

* §4 the node-list preparation stage, rebuilt.

* §5 the node-list validator over **both** repairs — the normalization fork of
  `CanonicalBooleanNodeListRebuildProgram` and the preparation fork of §4.
-/

namespace NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListRebuildProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalTaggedNatListRebuildProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## §1 The node validator, rebuilt -/

/-! ## §2 The node batch, rebuilt -/

/-! ## §3 The preparation fork, rebuilt -/

/-! ## §4 The node-list preparation stage, rebuilt -/

/-! ## §5 The node-list validator over both repairs -/

end NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram
