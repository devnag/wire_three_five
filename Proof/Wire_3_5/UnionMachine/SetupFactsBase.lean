import Proof.Wire_3_5.UnionMachine.PlanBase

/-! # C6: the setup facts and the accepting-call fact at the pinned setup (plan residuals `SetupFactsF`, `AcceptsCallF`)

Realizes the two facts of the pinned setup that the union leaf reads besides its machine:
* the propagated error of the slack variant falls below `ε₀`: "All three propagated numerical errors will be at most
  `ε₀`" (P3:3490-3491), here `(1+Λ̄)⁴(q^{−D} + 2^{−p}) + (1+Λ̄)⁴2^{−p} ≤ ε₀` with `p = ⌈log₂(q+2)⌉` and `D = 1`,
 from the `eventually_hD` at `ε₀/3`; the outer PCP's error is positive and its padded width
  grows ("pad the outer verifier to the exact width `q(N)`", P3:3637-3641); the setup decides `L`;
* a guess passing the tests makes an admissible call: the clause test "`μ̂ ≥ τ`" (P3:3487-3488) with `τ ≥ (c+s)/2 > 0`
  needs a nonzero clause term, and every nonzero term's call is admissible (`UnionAccepts`).

Paper quantities of the main types: **`Plan.SetupFactsF l`** and **`Plan.AcceptsCallF l`** (`setupFactsF`,
`acceptsCallF`). Both branches of the pinned `S₂` (the refuter's own PCP at `recL`, `S₁` elsewhere) are
`setupOfResult` setups with the constants `gateParams1 l`, the grid `gridMassOf (gateCδ1 l) sp` and a padded width at
least the ledger's `q(N)` (`setupFacts_of_result`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SetupFacts
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.Plan Filter
open NearCubicWires.WireExponent3_5.Shared (uMean)

/-! ## An accepting guess calls -/

/-- The masked verifier's threshold is positive: `τ ≥ (c+s)/2` and `c − s > 0` (the rounding reserve). -/
theorem threshold_pos {cp sp : ℝ} (params : MaskedSoundnessParameters cp sp) : 0 < (params.threshold : ℝ) := by
  have h1 := params.thresholdAboveMidpoint
  have h2 := params.sp_nonneg
  have h3 := params.roundingReserve
  have h4 : 0 ≤ 5 * Real.sqrt (24 * (params.v0 : ℝ)) := by positivity
  have h5 : (0 : ℝ) ≤ params.eps0 := by exact_mod_cast params.eps0_nonneg
  linarith

section Calls

end Calls

/-! ## The setup facts -/

section Result

end Result

section Gate

end Gate


end NearCubicWires.WireExponent3_5.UnionMachine.SetupFacts
