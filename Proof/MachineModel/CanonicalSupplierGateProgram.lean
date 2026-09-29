import Proof.Foundations.SupplierPipeline
import Proof.MachineModel.CanonicalIntPredecessorProgram

/-!
# Canonical supplier gate-field lowering

Supported normalized gates have one public canonical representation:
`[weights, threshold, support]`.  This fixed parser exposes those three wire
codes without decoding a semantic gate or accepting a host-built request.

The threshold is placed on the left of the output.  The next linked stage can
therefore transform it with `preserveRightProgram` while retaining the
weights/support context exactly once.
-/

namespace NearCubicWires.CanonicalSupplierGateProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalIntPredecessorProgram
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker

/-! ## Exact-decomposition request packing -/

/-! ## Shared compressed-gate primitives -/

end NearCubicWires.CanonicalSupplierGateProgram
