import Proof.SourceAssembly.SourcePhaseLoop

/-! # SP's per-clause exits, reduced to the source's final bank `values.A N`, `values.H N`

**Consumer.** SP's `SourceClauseExit` (`source-phase-20260923/SourcePhaseFrame.lean:138`) and
`SourceClauseAppend` (`Proof/SourceAssembly/SourcePhaseLoop.lean`), owed by the per-clause cycle (map rows E1–E6). Both
speak about the site's exit `globalAfter`/`globalHnext`. `SourceTrace` fixes that exit only through
`_hfinalA`/`_hfinalH`:
- `globalAfter = install whole queried (pad counterCaps (cfg 3 (state N [])).tapes)`;
- `globalHnext = dockH whole globalH (cfg 3 (state N [])).heads`;
- `state N = ⟨body.start, values.H N, padded N⟩`.

**What this module proves.**
- `final_tape`: every body tape BELOW `F = offset+1155` exits as `values.A N` on the same index (the reserve
  and the counter caps are `0` there).
- `final_head`: every source tape exits with head `values.H N`.
- `clause_exit` and `clause_append`: SP's two structures follow from facts about `values.A N` and
  `values.H N` alone. Those are properties of the source's own bank chain (first cycle, family, refill), which
  the construction controls.

**Paper.** None (machine layer). The consumer is SP's typed per-clause interface. **Budget**: none (no machine).
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction.ClauseBridge
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section bridge

end bridge

end
end NearCubicWires.SourceConstruction.ClauseBridge
end
