import Proof.MachineModel.TopDownPaidReusableFamily
import Proof.MachineModel.TopDownFamilyAuditContract

/-! Actual binary-order C.10 requests instantiate the reusable callback.
Value bounds and count congruence are the accepted source theorems; the
uniform printed width is the existing family contract's commonWidth. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator CanonicalFourfoldRowProgram ThresholdCompiler SourceInterfaces
open RepairSource CloseoutFinal
attribute [local irreducible] BinaryPool.pool CompactBounds.radix

variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)
  (harity : (s+1)/2+s/2=liveᶜ.card) (w degree : Nat)
  (hs : 67 ≤ s) (hpos : 1 ≤ w) (hload : 200*(live.card+w*(live.card+2)) ≤ s)

noncomputable def binaryDatum (d : P1TopDownFamilyAudit.Descriptor a live occ s w degree) (C : Nat) : Datum where
  row:=BinaryRequest.input a live occ s harity d.polynomial w degree hs d.monomials_fit hpos hload d.degree_fit
  C:=C
  Q:=live.card+1
  f:=C10SupplierTable.table a live occ s harity d.polynomial w hs d.monomials_fit hpos hload
  select:=d.select

end NearCubicWires.P1TopDownPaidReusable
