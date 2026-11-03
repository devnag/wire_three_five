import Proof.Packets.SrcEntryW4
import Proof.SourceAssembly.SourceStepsV5b
import Proof.SourceAssembly.SourceSkelOnsetW

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceStart.EntryW
open NearCubicWires.SourceSkeleton.FirstW
noncomputable section

section fam
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (code : SourceParent.CodeFamily mask selector packets rows
    (forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows)))

set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows)

def EWFam : SourceSteps.SiteFam mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) code :=
  fun sources gamma hg hh p n x bits hp =>
    EW selector xtra mask packets rows sources gamma hg hh p
      (PCJ374c44bb8b7f47d9_.S.mode sources p ((𝔉).capIndex sources gamma hg hh p + 1) (Nat.succ_pos _)
        (kSite selector xtra mask packets rows sources gamma hg hh p) (rSite selector xtra mask packets rows sources gamma hg hh p)
        (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp) n x bits

end fam

end
end NearCubicWires.SourceStart.EntryW
end

