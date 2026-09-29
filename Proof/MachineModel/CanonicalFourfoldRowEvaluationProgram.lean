import Proof.MachineModel.CanonicalFourfoldRangeRequestProgram
import Proof.MachineModel.CanonicalSupplierEnvelopeBottomProgram

/-!
# Canonical fourfold row evaluation

This module builds the production row evaluator only from fixed, verified
machine layers.  The first segment decodes the public five-field row request,
executes the typed circuit envelope and the imported exact-decomposition
runner, and retains the row/input coordinates beside the resulting bottom
forest.  No decoded host value or run-time compiler callback crosses this
boundary.
-/

namespace NearCubicWires.CanonicalFourfoldRowEvaluationProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalFourfoldRangeRequestProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalSupplierCircuitBatchProgram
open NearCubicWires.CanonicalSupplierCircuitBottomBatchProgram
open NearCubicWires.CanonicalSupplierEnvelopeBottomProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Row-envelope handoff -/

/-! ## Bottom-forest context projection -/

/-! ## Closed row-code to exact-bottom lowering -/

/-! ## Published typed row executions -/

/-! ## Range atom to verified bottom package

This is the first paper-specific vertical slice through the aggregation ABI.
It connects the fixed range-atom lowering directly to the existing typed
bottom evaluator; no host-built `FourfoldRowRequest` crosses the boundary. -/

end NearCubicWires.CanonicalFourfoldRowEvaluationProgram
