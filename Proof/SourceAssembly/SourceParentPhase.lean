import Proof.CaseAnalysis.FiveSourceTrace

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## Names for the consumer's `let`s (reducible, so they unfold to its terms) -/

abbrev Poly (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k den : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (bits : List Bool) (ph : Phase) :=
  CloseoutFinalC10Exactness.phasePolynomial ph (pcppAt sources k clock x oracle)
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits)
    (C10TotalDecode.Atom.systematic (pcpp := pcppAt sources k clock x oracle))

/-- Phase word bank `wordSlots ph` in the body layout. -/
abbrev Wd (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (k r scratch : Nat) (ph : Phase) :=
  CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
    (ControllerSelectedContinuation.bodyTapes sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
    (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch) ph

/-- The number of PCPP clause addresses of the actual request. -/
abbrev NC (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)) :=
  2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits

/-- The query-cache contents at clause `j` with EMPTY query word. -/
abbrev CD (sources : EightSources) (k : Nat) (clock : OrdinaryClock (fun n => n^(k+2)))
    {n : Nat} (x : BitInput n)
    (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
    (j : Nat) :=
  PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k clock x oracle)
      ((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)))
    (req sources k clock x oracle).arity j
    (PCPPQueryCachedBounds.capacity (CloseoutLanguage.selectedPCPP sources)
      ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)) []

/-! ## `PhaseWitness`: what one `MaskedPhase` still owes -/

end
end NearCubicWires.SourceParent
end
