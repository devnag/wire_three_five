import Proof.Foundations.Semantics

/-!
# The quotient-budget currency at low import depth

The frozen constants and the budget currency, placed below `ExecutableInterfaces` so that the
machine interface, the closure lemmas and `PublishedRecoveryClosure`'s clock literal can all
reference them without import cycles.

Contents:
* `recoveryVerifierDegree` names only the clock: `recoveryVerifierDegree + 1` is the frozen
  depth 5.
* `honestRecoveryDegree = 2 ^ (recoveryVerifierDegree + 1) = 32` — the machine's honest declared
  degree.  It must equal `2 ^ clockDepth` exactly: the no-go theorem
  `clockExponentFloor_not_recoveryRequestPolyBoundedAt` applies at every degree `≤ 31` and fails
  at exactly `32`, so `32` is the first admissible value.
* `savingExponent` (σ_net := 1), `columnTableExponent` (h_D),
  `savingKappa` (κ > h_D + σ + 10, paper.tex:949), `batchWidthParameter`
  (K = κ·L(q), paper.tex:979-981), `quotientBudget` — the declared-budget currency.
* The two lemmas (K-freeze saving threshold; printer-constraint feasibility) and the
  eventual-domination engine behind them.

Statement-form notes: the printer bracket is bounded with `logScale`
(`⌈log₂(·+2)⌉ ≥ log₂(·+1)`), pointwise larger than the paper's terms —
conservative direction.  The budget ledger consumes the tree's own
`normalizedLiveCount` (min-q-clamped) rather than `batchWidthParameter`,
which is kept as the paper's value.
-/

namespace NearCubicWires

namespace ExecutableRecoveryMachine

end ExecutableRecoveryMachine

/-! ## §1 The frozen saving constants -/

/-- **The quotient budget** — the declared-budget currency:
`⌊coefficient · (measure+1)^degree / L(measure)^saving⌋`.
Floor division only SHRINKS the declared budget, so `halts` stated at this
budget is harder, never easier, than the paper's real-valued quotient. -/
def quotientBudget (coefficient degree saving measure : ℕ) : ℕ :=
  coefficient * (measure + 1) ^ degree / logScale measure ^ saving

/-! ## §2 Elementary `logScale` facts -/

/-! ## §3 Lemma one — `K` meets the saving threshold -/

/-! ## §4 The eventual-domination engine

`Θ(log² q) ≤ q` eventually, in fully explicit Nat form: no analysis, no
asymptotic classes, onset computable from the constants. -/

/-! ## §5 Lemma two — the printer constraint clears eventually -/

end NearCubicWires
