import Proof.MachineModel.CanonicalBooleanNodeListValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram

/-!
# Canonical Boolean-circuit validation

The public circuit word is consumed by one fixed pipeline.  A fixed-arity
tuple parser exposes the node tree and output-index code, the total node-list
validator derives the exact node count, the shared Nat validator derives the
output index, and the sole native less-than path checks that the output names
an existing node.  No decoded circuit, node count, topology witness, or runtime
callback is accepted from the caller.
-/

namespace NearCubicWires.CanonicalBooleanCircuitValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBooleanNodeListValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed outer tuple and field projection -/

/-! ## Total node-list validation while preserving the output field -/

/-! ## Shared Nat validation on the machine-projected output field -/

/-! ## Machine-derived output-range request -/

/-! ## One fail-closed acceptance gate -/

/-! ## Unique total circuit validator -/

/-! ## Semantic soundness -/

/-! ## Typed-code refinement -/

end NearCubicWires.CanonicalBooleanCircuitValidationProgram
