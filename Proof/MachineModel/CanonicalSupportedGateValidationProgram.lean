import Proof.MachineModel.CanonicalBoolListValidationProgram
import Proof.MachineModel.CanonicalIntListValidationProgram

/-!
# Canonical supported-gate validation

A normalized supported gate is encoded by the fixed tagged tuple
`[weights, threshold, membership]`.  This module validates those heterogeneous
fields by composing the repository's unique signed-integer, integer-list, and
Boolean-list validators.  The output retains exactly the canonical field codes
needed by the subsequent length and support-relation stage.
-/

namespace NearCubicWires.CanonicalSupportedGateValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBoolListValidationProgram
open NearCubicWires.CanonicalIntListValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed gate tuple -/

/-! ## Tuple-field projection -/

/-! ## Heterogeneous field sequencing -/

/-! ## Exact staged field state -/

/-! ## Fail-closed field gate -/

/-! ## Unique composed field prefix -/

/-! ## Exact field semantics -/

end NearCubicWires.CanonicalSupportedGateValidationProgram
