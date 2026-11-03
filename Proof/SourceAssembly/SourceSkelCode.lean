import Proof.SourceAssembly.SourceRefillLoop
import Proof.SourceAssembly.SourceCodeFamily

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

structure RestData (a : DecompositionAlgorithm) where
  vE : PCJd4d1d9d7d1fa4313_Production.Request → Nat
  vP : PCJd4d1d9d7d1fa4313_Production.Request → Nat
  se : PacketsGlue.RequestMeta.UnaryStage a vE
  sp : PacketsGlue.RequestMeta.UnaryStage a vP
  gW : Nat

/-- `SourceWiring`'s rewind placement is injective. -/
theorem rewind2_injective {d : Dims} (e : d.Ext) {V : Nat} (hV : d.U ≤ V) :
    Function.Injective (Dims.rewind2Slots e hV) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := i.isLt; have hj := j.isLt; have := e.hF
  simp only [Dims.rewind2Slots, Dims.rw2V] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

section code

end code

/-! ## The mode-indexed code family at the forced choices -/

/-- The owed data, per parameter tuple (fixed before `n x bits`). -/
abbrev RestFam := (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
  Parameters sources gamma → RestData (decompositionOf sources)

end
end NearCubicWires.SourceSkeleton
end
