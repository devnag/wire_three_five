import Proof.Hierarchy.CompetitorCountTableRecord
import Proof.Hierarchy.CompetitorCountTableBounds

/-! Actual power-bin-lift rows discharge the count/congruence hypotheses
of the physical table-to-record caller. Its complete cost keeps the same
quadratic U factor and source-fixed short-width exponent. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
open LocalBitMultitape RecoveryRootRound RepairRepresentation MatrixScoreBatch
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def coefficient (a : WilliamsAlgorithm) := CompetitorCountTable.coefficient a+1034000
noncomputable def envelope (a : WilliamsAlgorithm) (r : Request) :=
  coefficient a*(r.U+1)^2*(r.d+r.p+1)^CompetitorCrossScheduler.exponent a

theorem budget_bound (a : WilliamsAlgorithm) (r : Request) (Q : ℕ) (hQ : Q≤r.p) :
    budget a r Q≤envelope a r := by
  have hwidth : Q≤CompetitorSameBucketColdDense.width r := by
    rw [CompetitorSameBucketColdDense.width_eq]
    omega
  have ht := CompetitorCountTable.budget_bound a r Q hwidth
  have hr := CompetitorCountRecordRequest.budget_bound r Q hQ
  have hp : (r.d+r.p+1)^2≤(r.d+r.p+1)^CompetitorCrossScheduler.exponent a :=
    Nat.pow_le_pow_right (by omega) (by unfold CompetitorCrossScheduler.exponent;omega)
  have hr' := hr.trans (Nat.mul_le_mul_left (1034000*(r.U+1)^2) hp)
  unfold budget envelope coefficient CompetitorCountTable.envelope at *
  nlinarith

end NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
