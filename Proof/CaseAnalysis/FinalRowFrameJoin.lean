import Proof.CaseAnalysis.CloseoutRowsEstimatorWarmRetained
import Proof.CaseAnalysis.FinalExternalRowLoop
import Proof.CaseAnalysis.FinalRowOrdering
import Proof.CaseAnalysis.FinalRoundBudget

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.RepairOrdinary.C10RowFrameJoin

open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CloseoutRowsEstimator
open CompetitorCrossScheduler (producer)
open NearCubicWires.ExtDecompositionBatch (Step dockH)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator
open NearCubicWires.RepairSource.CloseoutFinal.C10ExternalRowLoop
  (familyWriter familyFuel familyStream wordList pairList pairWord pairValue familyDenominator
    family_run)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule (widthPower)
open NearCubicWires.RepairSource.CloseoutFinal.C10RowOrdering
  (Round orderedPairList orderedWordList orderedFamilyStream orderedRow orderedPairList_growth
    ordered_family_run)

/-! ## 1. The reusable estimator bank's tape cover

`Reuse.tapes p` is `WholePrefix.tapes p + 1 + 2` and is partitioned by the five named slots plus
the `work` family; `WarmReuse.run` pins the heads everywhere and the tapes on `output`, `work`,
`driver` and `log`, while `WarmActual.native_run`/`capacity_run` pin the remaining two.  The cover
below is what turns those pins into a TOTAL exit tape function. -/

theorem tapes_ge (p : Program) : 70 ≤ WholePrefix.tapes p := by
  unfold WholePrefix.tapes; omega

/-! ## 2. The bank's entry and exit configurations, as named total functions -/

/-! ## 3. THE FRAME JOIN — a record-slot-only run as a FULL-configuration `Step`

`WarmActual.run` is stated at `WarmActual.entry`; `Step` is stated at
`⟨machine.start, hin, tin⟩`.  The two are the same configuration, which is the first lemma. -/

theorem hrow_of_step {t st : ℕ} (body : Machine t st)
    (source : ℕ → List Bool → Configuration t st) (emit : ℕ → List Bool) (cost len : ℕ)
    (hstart : ∀ k, k < len → ∀ pre, (source k pre).control = body.start)
    (hstep : ∀ k, k < len → ∀ pre, Step body cost (source k pre).heads (source k pre).tapes
      (source (k + 1) (pre ++ emit k)).heads (source (k + 1) (pre ++ emit k)).tapes)
    (k : ℕ) (hk : k < len) (pre : List Bool) :
    ∃ rc : ExecutionReceipt t st, runFrom body cost (source k pre) = some rc ∧
      rc.final.heads = (source (k + 1) (pre ++ emit k)).heads ∧
      rc.final.tapes = (source (k + 1) (pre ++ emit k)).tapes ∧ rc.steps ≤ cost := by
  obtain ⟨r, hr, hh, ht, hs⟩ := hstep k hk pre
  refine ⟨r, ?_, hh, ht, hs⟩
  have he : (⟨body.start, (source k pre).heads, (source k pre).tapes⟩ : Configuration t st)
      = source k pre := configuration_ext (hstart k hk pre).symm rfl rfl
  rwa [he] at hr

/-! ## 5. The round body, and the family loop it drives

The round body is the docked estimator bank followed by the INTER-ROW RE-LAY.  The re-lay is a
parameter with a named `Step` hypothesis, because nothing in the corpus produces it: round `k`
exits with every work tape `List.replicate D false` (`bank_row_step`) while round `k+1`'s entry
carries `WarmReuse.padded p D (Warm.input ... (row (k+1)) ...)`, the next printed row's bank.  That
is `paper.tex:2290-2296`'s \(q^{h_D}T_{\mathrm{prep}}\): the per-row preprocessing charge, taken
once per external row. -/

/-! ## 6. The resource statement — bucket ANALYSIS CALLS

`paper.tex:1409-1412` charges the analysis calls "and their remaining polynomial overhead" at
\(q^{p_{\mathrm{call},c}}\) times one residual cell, displayed at `paper.tex:1437-1439` and
aggregated at `paper.tex:1424-1425`.  `CloseoutFinalC10RoundBudget.WidthPoly`
(`Proof/CaseAnalysis/FinalRoundBudget.lean`) is that predicate and
`CloseoutFinalC10RoundBudget.WidthPoly.le_hotFuel` (`:254`) is its absorption into the cell
`hotFuel` (`Proof/CaseAnalysis/FinalCostAtTable.lean`).  This section composes with
those rather than redoing them; every quantity below is `k`-free (`k` occurs only as the width
index of `widthPower`, never inside a fuel).

**One observation for the consumer, because it changes what `roundFuel` has to be.**
`CloseoutFinalC10RoundBudget.roundFuel` (`Proof/CaseAnalysis/FinalRoundBudget.lean`) is
`clearedFuel decode + 1 + terms * (clearedFuel (termFuel w rows shift) + 1) + 1 + clearedFuel
cursor`, and its `rowAnswerFuel w rows` charges the SUMMATION over `rows` already-printed record
words -- it has no term for the family loop that PRINTS them.  `familyFuel_at_cell` is therefore an
ADDITION to that ledger, not a re-derivation of it; `WidthPoly.add`
(`Proof/CaseAnalysis/FinalRoundBudget.lean`) makes the addition free, because the absorption is
asymptotic and so insensitive to the constant.  **No band clear is added here**: the clear of this
segment is already inside `Reuse.budget` (`Proof/CaseAnalysis/RowsEstimatorReuseRun.lean`), whose
`afterBudget b D = 2*D + 40*b + 61` (`Proof/CaseAnalysis/RowsEstimatorReuseAfter.lean`) IS
`Reuse.after` = append-then-erase.  Charging `clearedFuel` again here would double-count. -/


end NearCubicWires.RepairOrdinary.C10RowFrameJoin
