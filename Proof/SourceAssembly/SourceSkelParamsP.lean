import Proof.SourceAssembly.SourceSkelParamsB
import Proof.Packets.SourceParams
import Proof.SourceAssembly.SourceCache

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton.Params
noncomputable section

def gwWS (mask : MaskProducer) : SourceBudget.ParNat := fun s _ _ _ _ =>
  2048 + 4 * mask.work + 4 * ExtDecompositionBatch.Cold.tapes (decompositionOf s) + 1024

theorem gwW_le_gwWS (mask : MaskProducer) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) (k : ℕ) (hk : k ≤ 512) :
    725 + 2 * mask.work + 2 * ExtDecompositionBatch.Cold.tapes (decompositionOf sources) + 2 * k ≤
      gwWS mask sources gamma hg hh p := by
  unfold gwWS; omega

def paramsP (selector : CyclicChoice.Laws) : ParamIn2 selector where
  cVc := SourceBudget.Params.cVcP selector
  hV := SourceBudget.Params.hVP selector
  y := SourceBudget.Params.siteY selector
  yF0 := SourceBudget.Params.siteYF0 selector
  I := SourceBudget.Params.siteI selector
  target := fun _ _ _ => SourceBudget.Params.tgOf
  smallDeg := fun _ packets rows => SourceBudget.DmOf packets rows SourceBudget.Params.degOf
  gwW := fun mask _ _ => gwWS mask
  polyC := SourceBudget.Params.gC selector
  polyE := SourceBudget.Params.gE selector

end
end NearCubicWires.SourceSkeleton.Params
end

