import Proof.Packets.BudgetJ5Loops

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size

/-- **The per-clause site fuel** at the base class `(d0 hT0 hS0 m L c0P c0T c0S)` of the three cycle costs, with the
calls-per-clause count `(q+1)^r` (coefficient `W^r`, `W = widthConst sources k`): the class of AD's
`siteFuel_inClasses` at `E ≤ W^r·(q+1)^r`, `E ≤ W^r·(n+1)^r`. -/
def siteRHS (sources : EightSources) (k r d0 hT0 hS0 m L c0P c0T c0S n qn : ℕ) : ℕ :=
  Admission.splitRHS (r+d0) (r+hT0) (r+hS0) m L
    (c0P + C10PartsSchedule.widthConst sources k^r*(c0P+c0P+4) + 4)
    (c0T + C10PartsSchedule.widthConst sources k^r*(c0T+c0T))
    (c0S + C10PartsSchedule.widthConst sources k^r*(c0S+c0S)) n qn

section clause

end clause

end
end NearCubicWires.SourceBudget
end

