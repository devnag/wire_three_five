import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorCircuitRebuildLedger
import Proof.MachineModel.CanonicalBooleanNodePrepareRebuildProgram

/-!
# The Boolean circuit validator, rebuilt a second time — and `hcall` re-landed

`ValidatorCircuitRebuildLedger` links the Boolean circuit validator's node-list
stage on `CanonicalBooleanNodeListRebuildProgram`'s first-generation repair, and
lands `hcall` on the two widths

* `booleanNodeListValidationRebuildBits`, and
* `canonicalNatValidationRebuildBits`.

`ValidatorPrepareRebuildWidthLedger` §7 **refutes** the first of those: its
preparation entry is the frozen `booleanNodeListPrepareBits`, which carries
`canonicalNatValidationBits` at every field of every structural descriptor, and
`ValidatorTaggedIntermediateVerdict` floors that charge at `2 ^ n` on the
canonical atom family.  So `hnode` is not open at the first-generation name; it
is false there.

`CanonicalBooleanNodePrepareRebuildProgram.booleanNodeListValidationPrepare-
RebuildProgram` replaces that program at an unchanged output contract —
`booleanNodeListValidationOutput inputLength raw`, the value the frozen and the
first-generation validators both return.  This module spends it: the circuit
validator's node-list stage is relinked on the second-generation validator, and
`ValidatorCircuitRebuildLedger` §1–§6 replays verbatim at the new callee, because
every stage above the swap is stated at the value the swapped callee returns.

The *natural* callee does not change: `canonicalNatValidationRebuildBits` is
already a rebuilt name and `ValidatorRebuiltWidthCertificates` isolates it as
`hnat`.

* §1 the second-generation node-list stage.

* §2 the second-generation Boolean circuit validator, executed.

* §3 the second-generation circuit width, reduced to two callee widths.

* §4 the reduced charge, in the domination judgement.

* §5 the second-generation oracle call.

* §6 `hcall`, at the second-generation node width and the rebuilt natural width.
-/

namespace NearCubicWires.ValidatorCircuitPrepareRebuildLedger

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodePrepareRebuildProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.ValidatorCanonicalizerRebuildLedger
open NearCubicWires.ValidatorCircuitLeafClosure
open NearCubicWires.ValidatorCircuitRebuildLedger
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCircuitWidthLedger
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorOracleCallWidth
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorWidthCombinatorLedger
open NearCubicWires.VerifiedLinker

/-! ## §1 The second-generation node-list stage -/

/-! ## §2 The second-generation Boolean circuit validator -/

/-! ## §3 The second-generation circuit width, reduced to two callee widths -/

/-! ## §4 The reduced charge, in the domination judgement -/

/-! ## §5 The second-generation oracle call -/

/-! ## §6 `hcall`, at the second-generation node width -/

end NearCubicWires.ValidatorCircuitPrepareRebuildLedger
