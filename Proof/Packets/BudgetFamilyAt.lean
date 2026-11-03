import Proof.Packets.BudgetFamilyCost
import Proof.Packets.BudgetEntryCount
import Proof.SourceAssembly.AdmissionCaps
import Proof.SourceAssembly.AdmissionSource

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

/-! ## 1. AD's constants, fixed from `(a, degree, target)` only -/

/-- AD's row-count coefficient (`rows_poly`). -/
def rowsC (a : DecompositionAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Admission.rows_poly a degree target)

/-- AD's row-count exponent (`rows_poly`; independent of `L` and `den`). -/
def rowsE (a : DecompositionAlgorithm) (degree target : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Admission.rows_poly a degree target))

/-- The cache-radix coefficient (`betaPoly_polynomial`). -/
def betaC (a : DecompositionAlgorithm) (degree : ℕ) : ℕ :=
  Classical.choose (Admission.betaPoly_polynomial a degree)

/-- The cache-radix exponent. -/
def betaE (a : DecompositionAlgorithm) (degree : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (Admission.betaPoly_polynomial a degree))

theorem betaPoly_le (a : DecompositionAlgorithm) (degree q : ℕ) :
    Admission.betaPoly a degree q ≤ betaC a degree * (q+1)^betaE a degree :=
  (Classical.choose_spec (Classical.choose_spec (Admission.betaPoly_polynomial a degree))).2 q

/-! ## 2. One admitted call: rows and row width -/

section call

end call

/-- The accuracy target of every source request. -/
abbrev tgt (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) : ℕ :=
  C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)

/-- The source's width exponent of the family fuel: row width `βE+2`, record width `r`. -/
abbrev famXE (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (r : ℕ) : ℕ :=
  betaE (decompositionOf sources) p.clauseDegree + 2 + r

/-- The source's width coefficient at the hierarchy index `k` (`W = widthConst sources k`, `Dw ≤ dC(b+1)`). -/
abbrev famXC (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r dC : ℕ) : ℕ :=
  (2*betaC (decompositionOf sources) p.clauseDegree + 10) *
      C10PartsSchedule.widthConst sources k^(betaE (decompositionOf sources) p.clauseDegree + 2) +
    (dC + 2)*(C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^r)

/-- **The family class at the source**: exponents from `rowsE`, `βE`, `r`, `hV` (all `k`- and `L`-free), coefficients
at `k`. S's base class must dominate it. -/
abbrev famClsAt (printer : WilliamsAlgorithm) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r cVc hV dC : ℕ) : CostCls :=
  famCls printer cVc hV
    (rowsC (decompositionOf sources) p.clauseDegree (tgt sources p) *
      C10PartsSchedule.widthConst sources k^rowsE (decompositionOf sources) p.clauseDegree (tgt sources p))
    (rowsE (decompositionOf sources) p.clauseDegree (tgt sources p))
    (famXC sources p k r dC) (famXE sources p r)

end
end NearCubicWires.SourceBudget
end

