import Proof.Circuits.ValidatorResidualLeafBudget

namespace NearCubicWires.ValidatorComputableLimitsAssembly

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
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The computable family as a limits function

The machine consumes a `limitsOf : ℕ → RecoveryWitnessLimits`; the computable
family is that function once its six parameters are given as functions of the
arity.  Nothing below constrains those parameter functions — they are exactly
where the schedule enters. -/

/-! ## §2 The two width premises the validator cannot pay

`hlength` is free: the request codec caps the public input length's width at
`4 · (measure + 1)`.  `hprefix` reduces to a statement about the family's own
serialized width — which §1 bounds by an explicit expression in the family's
parameters, so what is left mentions no validator definition at all. -/

end NearCubicWires.ValidatorComputableLimitsAssembly
