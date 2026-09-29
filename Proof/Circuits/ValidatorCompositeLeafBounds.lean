import Proof.Circuits.ValidatorLeafFuelBounds

namespace NearCubicWires.ValidatorCompositeLeafBounds

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableRecoveryMachine
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.RecoveryLimitsFrontEndProgram
open NearCubicWires.RecoveryVerifierResourceEnvelope
open NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## §1 The decoded list is the structural parse

`balancedValidationMapCodes` is the public decoder's output, and the public
decoder accepts only canonical codes — so whenever it accepts, the list it
returns is exactly the structural parser's atom list.  On a rejected code the
list is empty.  Either way its length is bounded by the parse's, which §2 of
`ValidatorLeafWidthCore` caps at twice the code's width. -/

/-! ## §4 The counted summary

The summary runs the map and then four counted post-passes — a balanced length
over the callee outputs, a nonzero count over the same outputs, a native
equality between the two resulting counts, and two constant gates.  Every one
of them is charged by the *output list's length*, which is the request list's
length, which is the decoded code list's length: §1's single number.  No
post-pass reads a callee output's magnitude, so the summary needs no width
certificate for the callee results at all, and its degree is the map's. -/

/-! ### The folded value's width -/

/-! ### The composite -/

/-! ### Field widths of a fixed-arity tagged tuple -/

/-! ### The rational validator's chain -/

/-! ### The three data-dependent stages -/

/-! ## §9 The machine-level corollary

With both premises delivered at `recoveryVerifierDegree` and at one coefficient,
`executableRecoveryMachineOfComponents` is applicable: the validator side of the
machine's resource ledger is *supplied*, not assumed.  Only the limits front end
and the semantic stage remain as the caller's obligations, exactly as
`RecoveryVerifierResourceEnvelope` intends. -/

end NearCubicWires.ValidatorCompositeLeafBounds
