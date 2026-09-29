import Proof.Circuits.ValidatorUnconditionalBudget

namespace NearCubicWires.ValidatorLeafPremiseSweep

open NearCubicWires
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.ValidatorUnconditionalBudget
open NearCubicWires.VerifiedLinker

/-! ## §1 The structural prefix's output

The nested-presence guard is a three-way rejection: it returns the handoff
unchanged or the closed numeral `0`.  So the prefix's output never exceeds the
handoff record, and `ValidatorStageEnvelopes` §4's trace ledger applies to it
verbatim. -/

/-! ## §2 The oracle stage's width

`recoveryOracleStageWidth` is a two-way maximum whose second entry is the
handoff itself, so §1 pays for half of it and the other half *is* `hresult`. -/

end NearCubicWires.ValidatorLeafPremiseSweep
