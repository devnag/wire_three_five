import Proof.Circuits.ValidatorTopologyRangeLedger

/-!
# `hcircuit`, closed

`ValidatorSweptLeafClosure` §3 lists `hcircuit` first: the Boolean circuit
validator's fuel charge at the oracle handoff.  `ValidatorCircuitStageWidths` §3
reduced it to two charges; `ValidatorNodePreparationLedger` §3 closed the first
and `ValidatorTopologyRangeLedger` §3 the second.  This module assembles them.

The one fact the assembly needs that no published module states is the *degree
anchor*: the oracle code the Boolean circuit validator runs on is a projection
of the **witness**, not of the serialized policy record.  So its width sits at
degree `1` — and that is what makes room for the preparation fork's degree-`3`
unit budget inside the published slot of `4`.  The projection is `private` to
`CanonicalRecoveryValidatorProgram`; `open private` reads it with no edit.

* §1 the degree anchor: `handoffOracleCode` of the structural prefix's output
  never exceeds the raw witness code.

* §2 the descriptor ledger: one structural node descriptor is linear in the
  atom it was parsed from, so the topology range's width hypothesis is paid
  from the node-list code's own width.

* §3 the node-list validator, assembled at degree `3`.

* §4 the Boolean circuit validator, assembled at degree `3`, and `hcircuit`
  itself at the machine's request family.
-/

namespace NearCubicWires.ValidatorCircuitLeafClosure

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.ValidatorCircuitStageWidths
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorDescriptionLeafClosure
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorNodePreparationLedger
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorResidualLeafBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorTaggedSpineLedger
open NearCubicWires.ValidatorTopologyRangeLedger

/-! ## §1 The degree anchor -/

/-! ## §2 The descriptor ledger -/

/-! ## §4 The Boolean circuit validator, and `hcircuit`

`booleanCircuitValidationFuel` is §3's charge under a wrapper, plus the
canonical natural stage and the comparison stage, both of which sit at the raw
code's own degree.  The whole charge lands at degree `3` — one inside the
published slot of `4`. -/

end NearCubicWires.ValidatorCircuitLeafClosure
