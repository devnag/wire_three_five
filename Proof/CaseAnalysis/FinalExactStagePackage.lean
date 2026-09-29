import Proof.CaseAnalysis.FinalCompletion
import Proof.CaseAnalysis.FinalStageFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal (constantsOf Parameters Runtime Theorem25Target
  theorem25_of_leaves)
open NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.RepairSource.CloseoutFinal.C10Fusion (Pipeline)
open NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdictUniform (tbud tailWidths'_of)
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (rowAnswer_le_rowDenominator)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ)

attribute [local irreducible] pcppOf Atoms

attribute [local semireducible] pcppOf Atoms

end

noncomputable section

/-! ## §6 The capstone anti-fork receipt -/

/-! **What is NOT compiled here, stated exactly.**  The three remaining data-level
identities -- `rawRealizes'` vs `rawRealizes`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`), `verdict_of_stage'` vs
`verdict_of_stage` (`:145`), and `machine_of_stage'` vs `machine_of_stage`
(`Proof/CaseAnalysis/FinalPipelineOfStage.lean`) -- are STATED at inputs this file
proves definitionally equal, but each was rejected by Lean as
`(deterministic) timeout at isDefEq` under the strict profile's 250000 heartbeats.
That is a budget fact about the size of the unfolding, not a counterexample, and
raising the limit is prohibited; the identities above `Realizes` are therefore
recorded as UNCHECKED rather than claimed. -/

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
