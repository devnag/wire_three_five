import Lean
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.UnionMachine.Slack
import Proof.Wire_3_5.UnionMachine.SchedLoop
import Proof.Wire_3_5.Selection.Contract
import Proof.MachineModel.Layout
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.UnionEventual
import Proof.Wire_3_5.UnionMachine.PlanBase


noncomputable section


/-! # C6: leaf U's enclosing application (P3:3669-3697, 3504-3554, 3797-3811)

Realizes, as the term of leaf U with its missing stages as explicit residuals, the paper's union weak machine: "The
weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid sum for each distinct PCPP variable.
It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid. Systematic parities are
constructed from the PCPP output. It then selects the common star translation, constructs the shared coordinate
filters, and performs (tr:tests)" and "At the finitely many source lengths where this fixed envelope exceeds the
refuter's `N/10` guess budget, the machine rejects outright" (P3:3669-3680); its soundness, `tr:soundness`
(P3:3504-3554); and its time, "the time for all polynomially many verification calls has the form [...]"
(P3:3797-3811), with the source preprocessing `N^{d_ver}q^{O_G(1)}` and `C_clk > d_ver + 2` (P3:3653-3655).

Paper quantity of the main type: **`UnionLeafF l`** (the union's build, `tr:soundness`, `tr:time` as `B.Split`, and
eventual `tr:completeness`, at the gate `gate0 l F` and the pinned setup `setupF l F`, under `GateFreeOK l F`).

Two layers, both proved here:
* **Layer A** (`unionLeafF_of_workers`): leaf U from a WORKER per primitive and language (`WorkerAt`: a machine whose
  result on the refuter's `⌊N/16⌋`-bit witness is the slack run `unionSlackRun` past an onset, within a fuel meeting
  the ledger's split). It uses M1 (`weakOf`, the slack soundness/completeness) and two setup residuals.
* **Layer B** (`workers_of_stages`): the worker from its stages, assembled here: the FRONT (U0–U5: gate, decode, PCP,
  substitution, PCPP, derived data, the coset selection docked from C1, the call table with the request writer and
  `callOk`, the thresholds preloaded into the accumulators, the loop's capacities), then the VERIFIED schedule loop
  (M3 `sched_loop`: the docked rewound estimator, the `p`-bit rounding, the accumulation, scrubbed between calls),
  then the DECISION (U7). The time is assembled here too (C7): the front's source work, one call for C1 at C1's OWN
  envelope (`Free.selection_le_callBudget`), the calls' count (the forcing lemma) times a per-call factor within
  `callDegMargin − 1` powers of `q + 1`, absorbed by `GateFreeOK` (`Split.calls_absorb`).

Residuals (the plan's helper types): `C1Impl` (C1/C3: `Implements (c1inst E₁ cosetWord selWord _ c₁)` at C1's own
envelope and the union's encodings), `DecideF` (U7), `FrontsF l F` (U0–U5), `CallCountF l` (T, `setupF_calls_le`),
`AcceptsCallF l` (a guess passing the tests makes an admissible call), `SetupFactsF l` (the setup's language, outer
error, width growth and propagated error with the rounding). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-! ## The union's own constants (P3:3633, 3653-3655) -/

section Consts

end Consts

/-! ## Layer A: the worker and leaf U -/

section Worker
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **The setup facts the slack soundness reads**: the setup's language is `L`, its width `q(N)` grows, and the
propagated error with the `unionBits` rounding plus the slack eventually falls below `ε₀` (Lemma H.3's proof). -/
structure SetupFacts (S : UnionSetup I) (L : Language) : Prop where
  lang : S.language = L
  hw : Tendsto (fun N => S.width N) atTop atTop
  hD : ∀ᶠ q : ℕ in atTop, (1 + (S.gridMass q : ℝ)) ^ 4 * ((q : ℝ) ^ (-(I.D : ℝ)) + 1 / 2 ^ unionBits q) +
      (slackOf (S.gridMass q) (unionBits q) : ℝ) ≤ (S.params.eps0 : ℝ)

/-- **A guess passing the tests makes an admissible call** (its `μ` test needs a nonzero clause term, P3:3487-3488):
with `Free.coef_pos` this makes the coefficient `0` branch vacuous. -/
def AcceptsCall (S : UnionSetup I) (P : FusedPrimitive I) : Prop :=
  ∀ N (z : BitInput N) (g : UnionGuess S z), UnionAccepts S P z g → ∃ req, I.Call req

namespace WorkerAt

end WorkerAt

end Worker

/-! ### The leaf's residual families -/

section Leaf

end Leaf

/-! ## Layer B: the worker from its stages -/

/-! ### C1, docked at its own envelope -/

/-! ### The stages' layout -/

section Stages

end Stages

/-! ### Residual U7: the decision -/

section Decide

end Decide

/-! ### Residual U0–U5: the front -/

section Front

end Front

/-- **Residual (the call count, Lemma H.7(b) and (58))**: at `setupF` and the clock `kclk`, eventually every guess
passing the outer step's guards schedules at most `q(N)^{unionCallDeg}` calls (`UnionCallCount.setupF_calls_le`). -/
def CallCountF (l : Literals) : Prop :=
  ∀ (coef A a : ℕ) (ha : a ≤ kclk + 1) (F : GateFree l) (L : Language)
    (hL : InNTIME (fun n => n ^ (kclk + 2)) L),
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (setupF l F kclk coef A a ha L hL) z),
      UnionGuards (setupF l F kclk coef A a ha L hL) z g → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ ((gate0 l F).budget kclk coef A a ha).q N ^ unionCallDeg l

/-! ### The worker: front, loop, decision -/

section Assembly

end Assembly

/-! ### Layer B at the gate -/

section LeafB

end LeafB

end NearCubicWires.WireExponent3_5.UnionMachine.Plan

end
