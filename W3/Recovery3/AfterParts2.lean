import W3.Recovery3.AfterParts
import Proof.CaseAnalysis.Capacity

-- Adapted from the gates module `Recovery.AfterParts2` to the narrow bundle `W3.Recovery3.{WS,WP}`.

/-!
# The recovery after the refuter: the stage workspace from the final address

The near-cubic-gates paper's uniform recovery (sec:all-lengths): stages 1 and 3 are "SAT formulas of size `2^{O(q)}`", and the whole recovery runs in
`2^{O(n)}` (`q ≤ m(q) ≤ n/2`). The after-prefix program supplies the stages' unary workspace `1^W` with proof 1's
capacity producer on the final address (`CloseoutCapacity`, `W = 2^{A n + B}`). `StageBudget d`: one `(A, B)` makes
`W` cover the three workspace hypotheses of `ENP.UStage.stage_run` for every width `R ≤ n`, and then one stage costs
at most `C (2^n + 1)^E`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery3.After

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.ENP

/-- **Stage workspace and cost from the final address** (paper §11.6, formulas of size `2^{O(q)}`, `q ≤ n`). -/
def StageBudget (d : ℕ) : Prop :=
  ∃ A B C E : ℕ, ∀ (n w R : ℕ) (vals : List Bool) (hw : w ≤ R) {m : ℕ} (x : BitInput m),
    R ≤ n → vals.length = 2 ^ w →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ CloseoutCapacity.capacity A B n ∧
    (DedupBytes.fields (unitPCP w vals)).length ≤ CloseoutCapacity.capacity A B n ∧
    2 ^ R ≤ CloseoutCapacity.capacity A B n ∧
    (0 < oracleSizeBound d R →
      UStage.cost d w R (CloseoutCapacity.capacity A B n) vals hw x ≤ C * (2 ^ n + 1) ^ E)

end NearCubicGates.Close.Recovery3.After
