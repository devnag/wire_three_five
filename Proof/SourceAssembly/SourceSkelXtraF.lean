import Proof.SourceAssembly.SourceSkelKeptW2
import Proof.SourceAssembly.SourceSkelFillV5
import Proof.Packets.SrcInitFitV4

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
namespace NearCubicWires.SourceSkeleton.XtraF
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

def h7q (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (mode : Bool) (ph : Phase) : ℕ :=
  Classical.choose (NearCubicWires.SourceStart.InitFitV4.H7_IKc4 selector mask packets rows sources gamma hg hh p
    (plSite selector (ResWin.xtraW selector) mask packets rows sources gamma hg hh p mode ph)
    (LW selector mask packets rows sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p))

/-- The H7 onset over all six `(mode, ph)`. -/
def q0H7 (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  max (max (h7q selector mask packets rows sources gamma hg hh p false .penalty)
      (max (h7q selector mask packets rows sources gamma hg hh p false .moment)
        (h7q selector mask packets rows sources gamma hg hh p false .clause)))
    (max (h7q selector mask packets rows sources gamma hg hh p true .penalty)
      (max (h7q selector mask packets rows sources gamma hg hh p true .moment)
        (h7q selector mask packets rows sources gamma hg hh p true .clause)))

def xtraF (selector : CyclicChoice.Laws) : XtraW selector := fun mask packets rows s g hg hh p =>
  max (ResWin.xtraW selector mask packets rows s g hg hh p)
    (Classical.choose (SourceBudget.widthAt_ge_eventually s (kW selector mask packets rows s g hg hh p)
      (q0H7 selector mask packets rows s g hg hh p)))

end
end NearCubicWires.SourceSkeleton.XtraF
end

