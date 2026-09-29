import Proof.MachineModel.ClosureRadixNative
import Proof.MachineModel.ClosureCompactSharedInput
import Proof.MachineModel.ClosureActualMaskDegree
import Proof.CaseAnalysis.FinalSupplierTable

/-! The literal C.10 request in the compact raw-stream writer's order.
This joins A.12's semantic count and its actual emitted header. The retained
metadata and raw source are still physical input obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactNativeRequest
open LocalBitMultitape RepairRepresentation RepairOrdinary
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput
open ExtIncidence RepairSource.VerifierDecoding

attribute [local irreducible] pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

theorem family_eq {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs]
    (rows : List (List (List Bool))) :
    P1CompactCloseoutRowsCacheInput.family gs rows = CloseoutRowsCacheInput.family gs rows := rfl

end NearCubicWires.P1Closure.CompactNativeRequest
