import Proof.SourceAssembly.SourceSkelFillW
import Proof.Packets.SrcMetaStepGF

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
namespace NearCubicWires.SourceSkeleton.FillV5
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsR (gWR)
open NearCubicWires.SourceSkeleton.ParamsV4 (LW fPW sfPW)
open NearCubicWires.SourceSkeleton.Fill (XtraW)
noncomputable section

def xRV5 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) : (mask : MaskProducer) →
    PCJc4297ab269d8423a_Source.PacketLibrary selector → PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  fun mask packets rows s g hg hh p =>
    xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) s g hg hh p +
      NearCubicWires.SourceStart.MetaStepGF.wMG selector s p packets (LW selector mask packets rows s g hg hh p)

theorem hxRV5 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) :
    ∀ mask packets rows sources gamma hg hh p, 2 ≤ xRV5 selector mask packets rows sources gamma hg hh p :=
  fun mask packets rows s g hg hh p =>
    le_trans (two_le_xROf (hRx4 selector mask packets rows) (SourceBudget.Params.hVN selector) s g hg hh p)
      (Nat.le_add_right _ _)

/-- The reserved region at v5. -/
abbrev resPV5 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) : ResChoice :=
  resR (gWR selector mask packets rows) (xRV5 selector mask packets rows)

abbrev G7HoleV5 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (xtra : XtraW selector) :=
  ∀ mask packets rows, RefillFamR mask packets rows (resPV5 selector mask packets rows) (fPW selector xtra mask packets rows)

abbrev FirstHoleV5 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (xtra : XtraW selector) :=
  ∀ mask packets rows, FirstFamR mask packets rows (resPV5 selector mask packets rows) (fPW selector xtra mask packets rows)

end
end NearCubicWires.SourceSkeleton.FillV5
end

