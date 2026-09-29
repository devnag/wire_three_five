import Proof.MachineModel.CanonicalBooleanCircuitPreparationProgram
import Proof.MachineModel.CanonicalBooleanNodeTopologyProgram

/-!
# Canonical Boolean-node-list validation

This module closes the raw balanced-list boundary in one path.  The machine
normalizes an arbitrary raw tree while independently checking canonicality,
derives the node count and sole structural descriptor stream, and checks every
descriptor at its machine-generated topological index.  No count, traversal
limit, descriptor list, or validation callback is accepted from the caller.
-/

namespace NearCubicWires.CanonicalBooleanNodeListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanCircuitPreparationProgram
open NearCubicWires.CanonicalBooleanNodeBatchProgram
open NearCubicWires.CanonicalBooleanNodeValidationProgram
open NearCubicWires.CanonicalBooleanNodeTopologyProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalForkCall
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalTaggedNatListValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PreserveRightProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.VerifiedLinker

/-! ## Canonicality and normalization from the same raw word -/

/-! ## Machine-derived count and descriptor tree -/

/-! ## Fixed topology-call lowering -/

/-! ## Fixed all-node topology call -/

/-! ## Machine-derived topology-count equality request -/

/-! ## Fixed equality call and final fail-closed gate -/

/-! ## Unique total node-list validator -/

/-! ## Typed-code refinement -/

end NearCubicWires.CanonicalBooleanNodeListValidationProgram
