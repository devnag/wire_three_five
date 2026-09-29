import Proof.Wire_3_5.UnionMachine.Plan

/-! # C6: the setup facts and the accepting-call fact at the pinned setup (plan residuals `SetupFactsF`, `AcceptsCallF`)

Realizes the two facts of the pinned setup that the union leaf reads besides its machine:
* the propagated error of the slack variant falls below `ε₀`: "All three propagated numerical errors will be at most
  `ε₀`" (P3:3490-3491), here `(1+Λ̄)⁴(q^{−D} + 2^{−p}) + (1+Λ̄)⁴2^{−p} ≤ ε₀` with `p = ⌈log₂(q+2)⌉` and `D = 1`
, from `eventually_hD` at `ε₀/3`; the outer PCP's error is positive and its padded width
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
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **An accepting guess makes an admissible call** (at every setup and primitive): with every clause coefficient `0`
the clause estimate `μ̂` would be `0 < τ`. -/
theorem acceptsCall_of (S : UnionSetup I) (P : FusedPrimitive I) : AcceptsCall S P := by
  intro N z g hg
  by_contra hno
  push Not at hno
  obtain ⟨-, -, -, -, -, hM, -, -, hμ⟩ := hg
  have hzero : ∀ i j t, (g.polyMuAt i).coeff j t = 0 := fun i j t => by
    by_contra h
    exact hno _ (hM i j t h)
  have h0 : g.μhat P = 0 := by
    unfold UnionGuess.μhat Poly4.estimate
    simp [hzero, uMean]
  have := threshold_pos S.params
  linarith

end Calls

/-! ## The setup facts -/

section Result
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)

/-- **The facts of a `setupOfResult` setup**: its language is `L`, and the width, outer error and propagated error
facts transfer from its data. -/
theorem setupFacts_of_result (L : Language) {T : ℕ → ℕ} (H : OrdinaryHierarchy T)
    (hL : ∀ n (x : BitInput n), L n x = true ↔ H.verifier.language H.time n x) {degrees : PCPDegrees}
    (P : OrdinaryPCPResult H degrees) (w : ℕ → ℕ) (hw : ∀ n, P.pcp.nativeWidth n ≤ w n) (a : PointwisePCPPAlgorithm)
    (G : ℕ) (params : MaskedSoundnessParameters a.completeness a.soundness) (gridMass : ℕ → ℚ)
    (hmass : ∀ q, 0 ≤ gridMass q) (gridSize : ℕ → ℕ) (hwt : Tendsto w atTop atTop)
    (hη : 0 < (params.outerError : ℝ))
    (hD : ∀ᶠ q : ℕ in atTop, (1 + (gridMass q : ℝ)) ^ 4 * ((q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ unionBits q) +
      (slackOf (gridMass q) (unionBits q) : ℝ) ≤ (params.eps0 : ℝ)) :
    SetupFacts (setupOfResult I L H hL P w hw a G params gridMass hmass gridSize) L :=
  ⟨rfl, hη, hwt, hD⟩

end Result

section Gate
variable (l : Literals)

theorem eps0_pos : 0 < ((gateParams1 l).eps0 : ℝ) := by
  have := gateEps_pos l
  show (0 : ℝ) < ((gateEps l ^ 2 / 20000 : ℚ) : ℝ)
  positivity

theorem outer_pos : 0 < ((gateParams1 l).outerError : ℝ) := by
  have := gateEps_pos l
  show (0 : ℝ) < ((gateEps l / 6 : ℚ) : ℝ)
  positivity

/-- **The propagated error with the rounding and the slack falls below `ε₀`** at the gate's grid (`D = 1`): three
times `(1+Λ̄)⁴q^{−1} ≤ ε₀/3`, since `2^{−⌈log₂(q+2)⌉} ≤ 1/q`. -/
theorem hD_gate (F : GateFree l) :
    ∀ᶠ q : ℕ in atTop, (1 + (gridMassOf (gateCδ1 l) (gate0 l F).row.sp q : ℝ)) ^ 4 *
        ((q : ℝ) ^ (-((1 : ℕ) : ℝ)) + 1 / 2 ^ unionBits q) +
      (slackOf (gridMassOf (gateCδ1 l) (gate0 l F).row.sp q) (unionBits q) : ℝ) ≤ ((gateParams1 l).eps0 : ℝ) := by
  have he : 0 < ((gateParams1 l).eps0 : ℝ) / 3 := by have := eps0_pos l; positivity
  filter_upwards [eventually_hD (gateZeta_pos l) (gateZeta_lt l) 1 le_rfl _ he, eventually_ge_atTop 1]
    with q hq hq1
  have hm : ((gridMassOf (gateCδ1 l) (gate0 l F).row.sp q : ℚ) : ℝ) =
      (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ) := by
    have := gridMassOf_rowB (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCδ1_pos l) q
    rw [show (gate0 l F).row.sp = rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) from rfl, this]
    push_cast
    rfl
  rw [slackOf_cast, hm]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hqr : (q : ℝ) ^ (-((1 : ℕ) : ℝ)) = 1 / q := by
    rw [Nat.cast_one, Real.rpow_neg_one, one_div]
  have ht : (1 : ℝ) / 2 ^ unionBits q ≤ 1 / q := by
    have h2 : q + 2 ≤ 2 ^ unionBits q := Nat.le_pow_clog (by norm_num) (q + 2)
    have h2' : (q : ℝ) + 2 ≤ 2 ^ unionBits q := by exact_mod_cast h2
    exact one_div_le_one_div_of_le hq0 (by linarith)
  rw [hqr]
  rw [Nat.cast_one, Real.rpow_neg_one, ← one_div] at hq
  set X := (1 + (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ)) ^ 4 with hX
  have hX0 : 0 ≤ X := by positivity
  have h3 := mul_le_mul_of_nonneg_left ht hX0
  nlinarith

end Gate


end NearCubicWires.WireExponent3_5.UnionMachine.SetupFacts
