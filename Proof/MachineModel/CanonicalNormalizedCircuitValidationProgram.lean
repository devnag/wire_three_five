import Proof.MachineModel.CanonicalSupportedGateRelationProgram

/-!
# Total normalized-circuit validation

The production validator shares one bottom-gate traversal across both
normalized circuit families.  This first layer is the common semantic
firewall: it validates every bottom gate at the declared arity while retaining
the mapped gate summaries, exact length, and original balanced tree for the
family-specific top validator.
-/

namespace NearCubicWires.CanonicalNormalizedCircuitValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBoolListValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## Exact four-field request prefix -/

/-! ## Shared header/bottom gate -/

/-! ## Single shared header/bottom executable -/

/-! ## Symmetric-family top validation -/

/-! ## Threshold-family top validation -/

/-! ## Fail-closed family dispatch -/

/-! ## Shared final packaging -/

/-! ## Unique production validator -/

/-! ## Exact family semantics -/

/-! ## Validated summary ABI

The single public validator output is
`pair familyTag (pair topSummary (pair bottomSummaryData rawCircuit))`.  Every
downstream resource reducer projects exactly those fields, so both the shape of
that value and the exact contents of its retained bottom-summary list are
established here, at the producing boundary.  No later stage reparses circuit
syntax, and nothing below unpairs a zero sentinel: each projection theorem
carries the owning gate's acceptance hypothesis. -/

/-! ### Typed field recovery

The canonical circuit codecs are injective on accepted codes, so a successful
decode determines the exact four request fields the validator projected.  These
lemmas are the only place where a typed circuit is related back to the request
syntax; the executable stages never repeat the comparison. -/

end NearCubicWires.CanonicalNormalizedCircuitValidationProgram
