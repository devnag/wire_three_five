import Proof.MachineModel.RuntimeShape
import Proof.Packets.BudgetJ5Loops
import Proof.SourceAssembly.SourceBundle
import Proof.SourceAssembly.SourceSkelTop

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
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size

section atK

end atK

/-- S's site class, per parameter tuple: EXPONENTS (and the divisor and live scale) fixed before the hierarchy
index, COEFFICIENTS at the index `k` (the type enforces the order of choices). -/
structure SiteClassFam where
  dS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  hT : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  hS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  m : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  L : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ
  cP : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ
  cT : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ
  cS : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ

/-- The schedule exponent (chosen before `k`). -/
abbrev rSel (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : ℕ :=
  (CloseoutFinalC10ModeNativeSchedule.selected sources p 0).exponent

section holes

end holes

end
end NearCubicWires.SourceBudget
end

