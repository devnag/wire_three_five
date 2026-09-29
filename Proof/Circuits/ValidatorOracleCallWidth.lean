import Batteries.Tactic.OpenPrivate
import Proof.Circuits.ValidatorCircuitLeafClosure

namespace NearCubicWires.ValidatorOracleCallWidth

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryLimitsComputableFamily
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorComputableLimitsAssembly
open NearCubicWires.ValidatorLeafPremiseSweep
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolicyWidthClosure
open NearCubicWires.ValidatorOracleResultWidth
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes

/-! ## §1 The native contextual call's width ledger -/

/-! ## §2 The validator's oracle call

At the validator's own call the five arguments are the public input length, the
handoff's two projections, the handoff itself and the oracle validation result
— and every one of those is bounded by the oracle stage's published width. -/

/-! ## §3 `hcall` at the machine's request family

The three width certificates the reduced ledger consumes are all published: the
request length's own width anchor, the structural prefix's output width, and the
oracle validation result.  So `hcall` costs exactly one new premise — the
Boolean circuit validator's register requirement. -/

end NearCubicWires.ValidatorOracleCallWidth
