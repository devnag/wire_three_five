import Proof.SourceAssembly.SourceSkelXtraF

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction
namespace NearCubicWires.SourceSkeleton.OnsetW
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
noncomputable section

/-- The worker's onset is past the continuation's base. -/
theorem base_le_onset (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : ℕ) (hden : 0 < den)
    (remainingDegree r base scratch : ℕ)
    (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      LocalBitMultitape.Machine (ControllerSelectedContinuation.bodyTapes sources p
        (ControllerCappedRuntime.hierarchyIndex sources p den remainingDegree) r scratch) states)
    (remainingFuel : ℕ → ℕ) :
    base ≤ (ControllerCappedSelected.workerData sources p den hden (ControllerCappedSelected.programData den
      (ControllerCappedRuntime.continuation sources p den remainingDegree r base scratch site remainingFuel))).onset :=
  le_trans (le_max_left _ _) (le_max_left _ _)

/-- At `fPW xtra` the base is past `extraW xtra`. -/
theorem extraW_le_base (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (res : ResChoice) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) :
    extraW selector xtra mask packets rows sources gamma hg hh p ≤
      (forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).base sources gamma hg hh p :=
  SourceBudget.extra_le_baseR _ _ _ sources gamma hg hh p

theorem extraW_le_of_onset (selector : CyclicChoice.Laws) (xtra : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (res : ResChoice) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
      LocalBitMultitape.Machine (ControllerSelectedContinuation.bodyTapes sources p
        (ControllerCappedRuntime.hierarchyIndex sources p
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).capIndex sources gamma hg hh p + 1)
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).remainingDegree sources gamma hg hh p))
        ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).r sources gamma hg hh p)
        ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).scratch sources gamma hg hh p)) states)
    (n : ℕ)
    (hn : (ControllerCappedSelected.workerData sources p
      ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).capIndex sources gamma hg hh p + 1)
      (Nat.succ_pos ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).capIndex sources gamma hg hh p + 1)
        (ControllerCappedRuntime.continuation sources p
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).capIndex sources gamma hg hh p + 1)
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).remainingDegree sources gamma hg hh p)
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).r sources gamma hg hh p)
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).base sources gamma hg hh p)
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).scratch sources gamma hg hh p) site
          ((forcedChoices mask packets rows res (fPW selector xtra mask packets rows)).remainingFuel sources gamma hg hh p)))).onset ≤ n) :
    extraW selector xtra mask packets rows sources gamma hg hh p ≤ n :=
  le_trans (extraW_le_base selector xtra mask packets rows res sources gamma hg hh p)
    (le_trans (base_le_onset sources p _ _ _ _ _ _ site _) hn)

def xtraF2 (selector : CyclicChoice.Laws) (o : XtraW selector) : XtraW selector :=
  fun mask packets rows s g hg hh p => max (XtraF.xtraF selector mask packets rows s g hg hh p) (o mask packets rows s g hg hh p)

/-- `o ≤ xtraF2 o`. -/
theorem o_le_xtraF2 (selector : CyclicChoice.Laws) (o : XtraW selector) :
    ∀ mask packets rows s g hg hh p, o mask packets rows s g hg hh p ≤ xtraF2 selector o mask packets rows s g hg hh p :=
  fun _ _ _ _ _ _ _ _ => le_max_right _ _

/-- Past the steps' guard, every folded onset is `≤ n`. -/
theorem o_le_of_onset (selector : CyclicChoice.Laws) (o : XtraW selector) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (n : ℕ)
    (hn : extraW selector (xtraF2 selector o) mask packets rows sources gamma hg hh p ≤ n) :
    o mask packets rows sources gamma hg hh p ≤ n :=
  le_trans (o_le_xtraF2 selector o mask packets rows sources gamma hg hh p)
    (le_trans (xtra_le_extraW selector (xtraF2 selector o) mask packets rows sources gamma hg hh p) hn)

end
end NearCubicWires.SourceSkeleton.OnsetW
end

