import Proof.SourceAssembly.SourcePhaseLoop

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section

/-! ## 1. The explicit entry bank on the selected body (generic in `t P extra`) -/

section generic

end generic

/-! ## 2. Row C1: `S.bank` is the explicit installed entry bank -/

section requestEq
open NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedSource
  NearCubicWires.RepairSource.SelectedRecoveryIntegration NearCubicWires.CanonicalWitnessCodec

end requestEq

section entry
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size
open NearCubicWires.RepairOrdinary.CloseoutWitness NearCubicWires.RepairSource.SelectedRecoveryIntegration
  NearCubicWires.CanonicalWitnessCodec

/-! ## 3. Row C2: the penalty entry (`FirstPhaseEntry`, docked) and the penalty loop start -/

end entry

/-! ## 4. Row C3: the moment/clause entry (focused cache erase) and their loop start -/

section later


end later

end
end NearCubicWires.SourcePhase
end
