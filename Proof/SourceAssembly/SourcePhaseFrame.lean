import Proof.SourceAssembly.SourceParent

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
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. The phase region, on plain numbers -/

/-- The phase region below the site's private universe `offset+1155`. -/
def Region (L v : Nat) : Prop := v < 278 ∨ v = L+53 ∨ (L+124 ≤ v ∧ v < L+1155)

theorem tailSlots_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (i : Fin 475) :
    Region L (CloseoutFinalC10RetainedPhaseFold.tailSlots L B hL hFresh i).val := by
  have hi := i.isLt
  unfold Region CloseoutFinalC10RetainedPhaseFold.tailSlots
  dsimp only
  split_ifs <;> omega

theorem phaseBank_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (ph : Phase) (i : Fin 278) :
    Region L (CloseoutFinalC10RetainedPhaseFold.phaseBank L B hL hFresh ph i).val := by
  have hi := i.isLt
  have hp := (C10TailUniformSlots.phaseIndex ph).isLt
  unfold Region CloseoutFinalC10RetainedPhaseFold.phaseBank
  dsimp only
  split_ifs <;> first | omega | (simp only; omega)

theorem wordSlots_region (L B : Nat) (hL : 301 ≤ L) (hFresh : L+1154 < B) (ph : Phase) (i : Fin 278) :
    Region L (CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i).val := by
  unfold CloseoutFinalC10RetainedPhaseFold.wordSlots
  split_ifs
  · exact tailSlots_region L B hL hFresh _
  · exact tailSlots_region L B hL hFresh _
  · exact phaseBank_region L B hL hFresh ph i

/-! ## 2. The region against the body layout: the query cache sits at `{0,1} ∪ [P, offset)` -/

section layout
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch : Nat)

theorem cache_range (mode : Bool) (i : Fin 19) :
    (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val < 2 ∨
    (302 ≤ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val ∧
      (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i).val <
        PCJda54a286946142d3_BranchPhases.offset sources p k r) := by
  have hp : 302 ≤ WorkspaceSelectedEntry.size sources k r p.clauseDegree := by
    unfold WorkspaceSelectedEntry.size
    omega
  have hc := (WorkspaceSelectedEntryReady.cache sources p k mode i).isLt
  change (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) < 2 ∨
    (302 ≤ (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) ∧
      (if (WorkspaceSelectedEntryReady.cache sources p k mode i).val<2 then
      (WorkspaceSelectedEntryReady.cache sources p k mode i).val else
      WorkspaceSelectedEntry.size sources k r p.clauseDegree+
        (WorkspaceSelectedEntryReady.cache sources p k mode i).val-2) <
        PCJda54a286946142d3_BranchPhases.offset sources p k r)
  dsimp only [PCJda54a286946142d3_BranchPhases.offset]
  split_ifs <;> omega

/-- A region tape other than `0, 1` is never a cache tape. -/
theorem not_cache (mode : Bool) (t : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    (h2 : 2 ≤ t.val) (hR : Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) t.val) :
    ∀ i, t ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch mode i := by
  intro i he
  have hc := cache_range sources p k r scratch mode i
  rw [← he] at hc
  unfold Region at hR
  omega

end layout

/-! ## 3. The per-clause exit fact the phase loop consumes (owed by the per-clause cycle) -/

/-! ## 4. The generic loop frame (over `s_next`) -/

/-! ## 5. The phase loop, from the per-clause exits -/

section phase
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {b siteFuel : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}

/-! ## 6. The consumer fields at the loop exit `A N`/`H N` -/

/-- Word slots at index `≥ 2` sit at tapes `≥ 2`. -/
theorem wd_ge_two (ph' : Phase) (i : Fin 278) (h2 : 2 ≤ i.val) :
    2 ≤ (Wd sources p k r scratch ph' i).val := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hi := i.isLt
  have hp := (C10TailUniformSlots.phaseIndex ph').isLt
  simp only [Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots, CloseoutFinalC10RetainedPhaseFold.tailSlots,
    CloseoutFinalC10RetainedPhaseFold.phaseBank]
  split_ifs <;> first | omega | (simp only; omega)

end phase

end
end NearCubicWires.SourcePhase
end
