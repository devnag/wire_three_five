import Proof.MachineModel.CanonicalSupplierGateProgram
import Proof.MachineModel.CanonicalSupportedGateRelationProgram

/-!
# Canonical support-compressed supplier gate decomposition

Top threshold gates must be decomposed over their physically retained bottom
coordinates.  This module first identifies the unique semantic compressed
gate.  Its executable path is built below from the existing field parser,
support compressor, threshold predecessor, request packer, and native caller;
none of those wire formats is decoded into a host-side gate.
-/

namespace NearCubicWires.CanonicalSupplierCompressedGateProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalIntPredecessorProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalSupplierGateProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalSupportedGateRelationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CompilerSemantics
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SupplierPipeline
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## Semantic support compression -/

/-! ## Sole executable compressed-gate path -/

end NearCubicWires.CanonicalSupplierCompressedGateProgram
