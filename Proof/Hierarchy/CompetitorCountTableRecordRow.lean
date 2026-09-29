import Proof.Hierarchy.CompetitorCountTableRecord

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

end NearCubicWires.RepairOrdinary.CompetitorCountTableRecord
