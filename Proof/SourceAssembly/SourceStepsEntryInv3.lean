import Proof.SourceAssembly.SourceStepsEntryInv2

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 400000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section inv3
open NearCubicWires.SourceConstruction.InitRun

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- **The emitter/appender words on the site's `encT` tapes** (SI `InitOutM`'s form), all heads `0`, and the carried payload on `encT 5`. -/
def EncWords {d : SourceConstruction.Dims} {T : Nat} (hT : d.U ≤ T) (Rc b : Nat) (H : Fin T → ℕ) (A : Fin T → List Bool) : Prop :=
  (∀ kk : Fin 13, H (Dims.encT (d := d) hT kk) = 0) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (old : List Bool),
    A (Dims.encT (d := d) hT 3) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 3) ∧
    A (Dims.encT (d := d) hT 6) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 7) ∧
    A (Dims.encT (d := d) hT 7) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 8) ∧
    A (Dims.encT (d := d) hT 8) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 9) ∧
    A (Dims.encT (d := d) hT 9) = ZeroPadding.pad Rc (e_bank b en (D0 b) (cap0 b) old 10)) ∧
  (∀ (en : CloseoutRowsEstimatorCoefficients.Stream.Entry) (xs : List CloseoutRowsEstimatorCoefficients.Stream.Entry),
    A (Dims.encT (d := d) hT 10) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 2) ∧
    A (Dims.encT (d := d) hT 11) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 4) ∧
    A (Dims.encT (d := d) hT 12) = ZeroPadding.pad Rc (CloseoutFinalC10AppendPositioning.tapes b (D0 b)
      (CloseoutFinalC10AppendWorkspaceInit.capacity b) (CloseoutFinalC10AppendWorkspaceInit.capacity b) en xs 5)) ∧
  (∃ w : List Bool, w.length ≤ D0 b ∧ A (Dims.encT (d := d) hT 5) = ZeroPadding.pad Rc w)

end inv3

section bridge3

end bridge3

end
end NearCubicWires.SourceSteps
end
