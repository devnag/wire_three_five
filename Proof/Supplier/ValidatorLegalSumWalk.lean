import Proof.Circuits.ValidatorStageEnvelopes

namespace NearCubicWires.ValidatorLegalSumWalk

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The nine-node chain, named

`recoveryLegalSumEnvelopeFuel` links ten sub-stage charges through nine
`linkFuel` nodes.  The `n`-th node's second program is the tail of the chain
below it, so the nine tails are one another's suffixes; naming them once keeps
the chain coefficient readable and, more importantly, lets the chain lemma be
instantiated at *explicitly supplied* program arguments, so no metavariable is
ever solved by unfolding a composed `programRegisterSpan`. -/

/-! ## §2 The eleven-way maximum, named

The width side of the chain is a maximum, so it costs no coefficient at all: a
uniform envelope for the eleven entries *is* an envelope for the chain, at the
same coefficient and the same degree. -/

/-! ## §3 The chain coefficient of an arbitrary linker chain

Every sub-stage of the legal-sum envelope is itself a right-nested `linkFuel`
chain, so one list-indexed coefficient serves them all.  `chainCoefficient` is
the exact expression a cascade of `linkFuel_polyBounded` applications produces
at a uniform stage coefficient: reading the spans off the chain's tails from the
outside in, each node contributes its own span, the linker's `5`, and one copy
of the stage coefficient, and the innermost node contributes one extra copy for
the terminal charge.

The list is a list of *closed* natural numbers over composed programs.  It is
consumed only by `List.foldr`, whose reduction is structural in the list, so no
`programRegisterSpan` is ever evaluated. -/

end NearCubicWires.ValidatorLegalSumWalk
