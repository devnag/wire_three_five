import Proof.SourceAssembly.SourceSkelResWin
import Proof.SourceAssembly.SourceSkelFirstW

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton.KBound
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceConstruction
noncomputable section

theorem rBsel_ge (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : 3 ≤ SourceSteps.rBsel sources p := by
  unfold SourceSteps.rBsel
  exact le_trans (by omega) (le_max_right _ _)

theorem remDegR_ge (Q : SourceBudget.SiteClassFam) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : 19 * SourceSteps.rBsel sources p ≤ SourceBudget.remDegR Q sources gamma hg hh p := by
  unfold SourceBudget.remDegR
  omega

/-- **The site's hierarchy index is at least `57`.** -/
theorem kW_ge (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    57 ≤ kW selector mask packets rows sources gamma hg hh p := by
  have h1 := rBsel_ge sources p
  have h2 := remDegR_ge (SourceBudget.SiteClassFam.ofBaseR (BordW selector mask packets rows)) sources gamma hg hh p
  have h3 : SourceBudget.remDegR (SourceBudget.SiteClassFam.ofBaseR (BordW selector mask packets rows)) sources gamma hg hh p ≤
      kW selector mask packets rows sources gamma hg hh p := by
    unfold kW SourceBudget.kSelR SourceParent.kOf ControllerCappedRuntime.hierarchyIndex WorkspaceSelectedEntryRuntime.degree
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  omega

end
end NearCubicWires.SourceSkeleton.KBound
end

