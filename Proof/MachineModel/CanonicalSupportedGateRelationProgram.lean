import Proof.MachineModel.CanonicalNativeCallProgram
import Proof.MachineModel.CanonicalSupportedGateValidationProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Canonical supported-gate relations

The field validator establishes canonical syntax.  This module checks the
dependent gate relations: both vectors have the public arity, and every weight
outside the declared support is zero.  Support checking reuses the production
support compressor and the shared nonzero counter; it does not introduce a
second list traversal or decoder.
-/

namespace NearCubicWires.CanonicalSupportedGateRelationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.CanonicalSupportedGateValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## Semantic support invariant -/

/-! ## Canonical field payload adapters -/

/-! ## Exact public-arity validation -/

/-! ## Compression and zero-outside count framing -/

/-! ## Guarded zero-outside executable -/

/-! ## Length-guarded relation -/

/-! ## Total raw-code relation validator -/

/-! ## Exact relation semantics -/

end NearCubicWires.CanonicalSupportedGateRelationProgram
