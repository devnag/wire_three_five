import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalNormalizedCircuitValidationProgram
import Proof.MachineModel.CanonicalSupplierCompressedGateProgram

/-!
# Exact wire resources from validated normalized-circuit summaries

The normalized-circuit validator already emits everything needed for the
physical wire metric: each bottom-gate summary contains its support count, and
the threshold-family top summary contains the exact membership vector.  This
module consumes only that validated summary ABI.  It does not decode circuit
syntax again.
-/

namespace NearCubicWires.CanonicalNormalizedCircuitResourceProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNormalizedCircuitValidationProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupplierCompressedGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## One bottom-gate wire contribution -/

/-! ## Shared summary map and sum -/

-- Treat the verified map as an atomic linker stage downstream.  Its expanded
-- controller is large and no later proof may rely on its instruction layout.

/-! ## Threshold-family support selection -/

/-! ## Validated-summary dispatcher

The validator's public result is
`pair familyTag (pair topSummary (pair bottomSummaryData rawCircuit))`.
This final adapter only projects that ABI.  It never parses the normalized
circuit syntax or revalidates a gate.
-/

-- The family dispatcher is a verified stage boundary.  Downstream composition
-- depends on its contract, never on either expanded branch controller.

end NearCubicWires.CanonicalNormalizedCircuitResourceProgram
