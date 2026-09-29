import Proof.MachineModel.CanonicalSupplierCircuitBatchProgram
import Proof.MachineModel.CanonicalSupplierCircuitBottomBatchProgram

/-!
# Canonical supplier envelope-to-bottom decomposition

The canonical envelope batch already returns one balanced forest of native
circuit headers beside the single outer `(mode, q)` context.  This module
links that output directly to the sole circuit-bottom batch program through
`preserveRightProgram`; no request framing or decoder is duplicated here.
-/

namespace NearCubicWires.CanonicalSupplierEnvelopeBottomProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalSupplierCircuitBatchProgram
open NearCubicWires.CanonicalSupplierCircuitBottomBatchProgram
open NearCubicWires.CanonicalSupplierCircuitHeaderProgram
open NearCubicWires.CanonicalSupplierGateBatchProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Published-family bottom views -/

/-! ## Unique envelope-to-bottom composition -/

/-! ## Published canonical Fourfold envelopes -/

end NearCubicWires.CanonicalSupplierEnvelopeBottomProgram
