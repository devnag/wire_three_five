import Proof.Circuits.ValidatorPolynomialDomination

namespace NearCubicWires.ValidatorStageEnvelopes

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalRecoveryProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## §0 Width utilities

The binary width of a projection is the width of the projected code, and the
width of a pair is at most twice the larger component width.  These are the
only two facts the stage walks need about codes. -/

/-! ## §1 The native call and the native contextual call

`nativeCallFuel` is one `balancedCallFuel` at the *singleton* request list,
wrapped in two linkers; `nativeContextCallFuel` adds a framing adapter and the
context-preserving wrapper.  The request count is the closed numeral `1`, so
neither node raises the degree: this is the only place in the validator's cone
where a balanced call is *not* degree-raising, and it is why the oracle stage
costs exactly the degree of the circuit validator it calls. -/

/-! ## §4 The structural prefix's register requirement

`recoveryValidatorStructuralPrefixBits` is a three-way maximum over the public
input width, the nested-handoff ledger and the width of the handoff record.
Every register the prefix materializes is a projection of the raw witness code,
the serialized policy record, or a pairing of at most four of them, so the whole
stage is bounded — unconditionally — by a fixed multiple of one width
parameter.  This is the ingredient §4 of the domination module identified as
not being an executable stage's own charge. -/

/-! ## §5 The legal-sum envelope, the dominant stage

`recoveryLegalSumEnvelopeFuel` is a nine-node `linkFuel` chain over ten
sub-stage charges, and `recoveryLegalSumEnvelopeBits` is the matching eleven-way
maximum.  Six of the ten charges — and six of the nine linked programs — are
`private` to `CanonicalRecoveryValidatorProgram`, so a *named* walk of the chain
is not available outside that module.  What is carried here instead is the
chain's algebra, in the exact shape the definition has, plus the reductions for
the sub-stages that are public.

`legalSumChainFuel_polyBounded` is the nine-node instance of
`linkFuel_polyBounded`: a uniform envelope for the ten charges is an envelope
for the chain, at the same degree, with the coefficient
`legalSumEnvelopeCoefficient`.  It is stated over *variables*, so it applies to
the real definition by unification without any private name being written. -/

/-! ### The public sub-stages of the legal-sum chain

Two of the ten charges are closed numerals; two more are a
context-preserving wrapper around a native call, so §1 applies and both are
degree-preserving over their own list callee. -/

end NearCubicWires.ValidatorStageEnvelopes
