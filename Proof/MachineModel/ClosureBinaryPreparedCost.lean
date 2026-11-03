import Proof.MachineModel.ClosureBinaryPreparedWriter
import Proof.CaseAnalysis.RowsCapacityDriver
import Proof.CaseAnalysis.RowsPolynomial
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.MachineModel.ClosureCompactFamily
import Proof.MachineModel.ClosureCompactMetadata
import Proof.MachineModel.ClosureRadixNative
import Proof.MachineModel.ClosureRawRelabelFamily
import Proof.MachineModel.NativeFamily
import Proof.MachineModel.ClosureCompactCacheCost

/-! The actual prepared binary writer is bounded from the original cache,
original polynomial degree, and lowered monomial count. No packet-specific
size premises or already relabelled input are assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPreparedCost
open RepairOrdinary RepairRepresentation ExtIncidence
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

end NearCubicWires.P1Closure.BinaryPreparedCost
