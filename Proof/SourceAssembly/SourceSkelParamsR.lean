import Proof.SourceAssembly.SourceSkelClassR
import Proof.SourceAssembly.SourceSkelGenS
import Proof.SourceAssembly.SourceSkelParamsP
import Proof.SourceAssembly.SourceSkelParams

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
namespace NearCubicWires.SourceSkeleton.ParamsR
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params
noncomputable section

variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-! ## 1. The site class and its live scale at `rB` -/

/-- The site's accuracy target. -/
abbrev TR : SourceBudget.ParNat := SourceBudget.Params.tgOf

/-! ## 2. `den0` -/

/-! ## 3. The init's windows at `rB` -/

/-! ## 4. `extra` at `rB` -/

/-- AD's input-length coefficient / exponent at the site's target. -/
def inCR (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  Classical.choose (Admission.input_poly (decompositionOf sources) p.clauseDegree (TR sources gamma hg hh p))
def inER (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  Classical.choose (Classical.choose_spec (Admission.input_poly (decompositionOf sources) p.clauseDegree (TR sources gamma hg hh p)))

/-! ## 5. The reduce term -/

abbrev gWR : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  gWP (paramsP selector).toParamIn

end
end NearCubicWires.SourceSkeleton.ParamsR
end

