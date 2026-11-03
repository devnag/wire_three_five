import Proof.MachineModel.ClosureBinaryReusableRow
import Proof.CaseAnalysis.RawRowsLoad
import Proof.CaseAnalysis.RowsUniversalResources
import Proof.MachineModel.P1ClosureCompactCost

/-! Actual binary-row driver accounting: header support stays linear and
additive, cut scanning retains load slack, and the signed table appears once.
The source radix and original degree, not the replicated pool, price p. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryRowCost
open RepairRepresentation RepairOrdinary ExtIncidence
open SupplierPipeline SupplierEstimator ThresholdCompiler CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal C10SupplierRowInput CloseoutRowsEstimator

attribute [local irreducible] pool BinaryPool.pool bank childList CompactBounds.radix
  CloseoutRowsUniversal.pool ExtDecompositionBatch.GS

variable {q : Nat} (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)
  (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (P : StructuralGF2Polynomial) (w degree : Nat)
  (hs : 67 ≤ s) (hmon : (CloseoutRowsUniversal.lower a live occ P).length < 2^w)
  (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)
  (hdegree : CloseoutRawRows.RawMonomialDegreeAtMost degree P)

local notation "row" => BinaryRequest.input a live occ s harity P w degree hs hmon hpos hload hdegree

end NearCubicWires.P1Closure.BinaryRowCost
