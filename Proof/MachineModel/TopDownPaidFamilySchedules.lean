import Proof.MachineModel.TopDownPaidFamilyRows

/-! The original ordered external-row schedules, instantiated with real
binary C.10 requests. The emitted list is the exact parent's payload list. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask RecoveryRootRound P1Closure
open SupplierPipeline SupplierEstimator SupplierPrime SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource CloseoutFinal CloseoutRawRows
open C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow
open C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord
attribute [local irreducible] BinaryPool.pool CompactBounds.radix
  symDatum thrDatum familyPolynomial pairList

section Sym

end Sym

section Thr

end Thr

end NearCubicWires.P1TopDownPaidReusable
