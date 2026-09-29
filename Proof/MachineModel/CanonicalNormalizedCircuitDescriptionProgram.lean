import Proof.MachineModel.CanonicalNormalizedCircuitResourceProgram

/-!
# Exact description size from validated normalized-circuit summaries

The normalized-circuit validator is the sole syntax boundary.  Its gate summary
retains the threshold, the weights selected by the support mask, and the exact
support count.  Validation also proves every omitted weight is zero, so this
module restores their one-bit charge without parsing the circuit again.
-/

namespace NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNormalizedCircuitValidationProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## Canonical signed-integer bit charge -/

-- Link normalization expands the audited balanced-length controller.

/-! ## Exact sum over a validated integer-code tree -/

-- Downstream links use these verified contracts, never their expanded bodies.

/-! ## One validated normalized gate -/

/-! ## Bottom-gate map and sum -/

/-! ## Family branches -/

/-! ## One validated-summary dispatcher -/

/-! ## Typed semantic refinement -/

end NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram
