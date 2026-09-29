import Proof.Circuits.ValidatorCompositeLeafBounds

namespace NearCubicWires.ValidatorResidualLeafBudget

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalRationalMassProgram
open NearCubicWires.CanonicalRecoveryValidatorProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorLegalSumWalk
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The canonical rank selector's counting ledger

The selector walks the same pending-subtree stack the nonzero counter walks,
and charges a constant per decoded node.  The requested rank is carried along
and only ever *decremented*, so it never enters the charge: the bound below is
uniform in `rank`, which is exactly what §2 needs to charge the counted call
without a per-request certificate. -/

/-! ### The compression pipeline

Five nodes: the shared count preparation, the generated range builder, the two
counted calls above under their context-preserving wrappers, and one closed
numeral.  Only the two counted calls raise the degree, and each raises it by
exactly the support-count's degree. -/

/-! ### The mass stage's own charge

`initializedRationalMassFoldFuel` is the fold's charge one step past the
accumulator installation, and `recoveryLegalTermMassFoldStageFuel` is that under
a context-preserving wrapper.  With the fold's budget derived, the validator's
mass fold stage closes from the summaries' denominator caps alone. -/

end NearCubicWires.ValidatorResidualLeafBudget
