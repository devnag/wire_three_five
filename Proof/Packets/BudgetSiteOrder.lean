import Proof.Packets.BudgetJ5Site
import Proof.Packets.BudgetJ5Skel

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

/-- A per-parameter natural number (exponents, onsets, indices). -/
abbrev ParNat : Type :=
  (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ

/-- A per-parameter coefficient, read at the hierarchy index `k`. -/
abbrev ParCoef : Type :=
  (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 → Parameters sources gamma → ℕ → ℕ

def liveOf (hT : ParNat) : ParNat := fun sources gamma hg hh p =>
  rSel sources p + (rSel sources p + hT sources gamma hg hh p) + SelectedRuntime.sigma sources + 2

/-- **`capIndex`** from an admission threshold `den0` (chosen after the live scale): the carried denominator of the
site is `capIndex + 1 ≥ den0`. -/
def capIndexOf (den0 : ParNat) : ParNat := fun sources gamma hg hh p => den0 sources gamma hg hh p - 1

theorem den0_le (den0 : ParNat) (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : den0 sources gamma hg hh p ≤ capIndexOf den0 sources gamma hg hh p + 1 := by
  unfold capIndexOf
  omega

end
end NearCubicWires.SourceBudget
end

