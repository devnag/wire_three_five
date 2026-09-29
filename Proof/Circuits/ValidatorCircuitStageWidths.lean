import Proof.Circuits.ValidatorResidualLeafBudget

/-!
# The Boolean circuit validator's counting stages

`ValidatorResidualLeafBudget` §5 walked `booleanCircuitValidationFuel` down to
exactly two named fuel charges, one comparison stage and two width
certificates.  This module discharges the comparison stage and both width
certificates; the two remaining fuel charges are named precisely at the end,
together with the *one* missing counting ledger each of them needs.

Both width certificates are the same fact twice: the counts the circuit
validator compares are **decoded-list lengths**, and `ValidatorLeafWidthCore`
§2 caps a decoded list's length at twice the code's width.  Nothing here reads
a decoded magnitude.

* §1 identifies the node count as the structural parse's atom count, and the
  topology count as a nonzero count over a request list of that same length.
  Both are therefore capped by the code's width, which is the certificate
  `booleanNodeListTopologyEqualityFuel_polyBounded` consumes.

* §2 discharges the comparison stage `booleanCircuitLtStageFuel`.  It is one
  native call into the published width-linear comparator, so it costs a closed
  program-shape overhead plus a multiple of the compared operands' widths — and
  both operands are counts capped by §1 or by the canonical natural validator's
  own candidate bound.

* §3 records what is left of the Boolean circuit validator, with the single
  missing ledger named for each.
-/

namespace NearCubicWires.ValidatorCircuitStageWidths

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanCircuitValidationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorResidualLeafBudget
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The two compared counts

The node-list validator compares two numbers: how many descriptors the
structural parse produced, and how many of them the topology pass accepted.
The first *is* the atom count; the second is a nonzero count over a request
list of exactly that length.  So one counting ledger pays for both. -/

/-! ## §2 The comparison stage

`booleanCircuitLtStageFuel` is one `nativeLtRequestFuel` under a
context-preserving wrapper, and `nativeLtRequestFuel` is a native call at a
singleton request list into the published width-linear comparator.  Both
compared operands are counts: the canonical natural validator's decoded value,
capped by its own candidate bound, and the node count of §1. -/

end NearCubicWires.ValidatorCircuitStageWidths
