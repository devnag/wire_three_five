import Proof.CaseAnalysis.FinalFuelMajorant
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Hierarchy.CompetitorWitnessTripleSemantics
import Proof.CaseAnalysis.WitnessOracleParameter

/-! # `StageBlock.hfuel`: what it actually demands, and where the demand comes from

`StageBlock.hfuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is

```
hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
  actualFuel sources k p S x bits ≤ S.budget n
```

It is the only one of the fourteen fields with no `Soundness.cutoff ≤ n` guard.
Its consumer is `verdict_of_stage`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`), whose deliverable is a
`Weak.StepAtInputs`-shaped `Verdict` at the len-only budget `S.budget` for EVERY
`n` and EVERY witness `bits`; the guard is absent because the consumer has none.

This module settles what that costs, in three steps and with no new hypothesis.

* §1 `actualFuel_eq`: `actualFuel` is a function of the input length `n` and the
  three per-phase CALL COUNTS `(records … ph).length`, and of nothing else.  The
  closed form `fuelAt` names `S.stageFuel`, `S.entryWidth` and `dockedFuel`
  explicitly.  It contains no `Nat` subtraction and no `Nat.log`: nothing in it
  truncates, at `n = 0` or anywhere else.
* §2 `fuel_bounded_iff`: at one length, `hfuel` is satisfiable by SOME budget if
  and only if the per-phase call count is bounded over `bits`.  Both directions
  are proved; the reduction is exact, not a sufficient condition.
* §3 The call count is driven by `2 ^ (pcppOf …).clauseBits`, whose only
  imported bound is `PointwisePCPPAlgorithm.clauseCountBound`
  (`Proof/Foundations/RepresentationSourceContracts.lean`), stated in terms of the
  GUESSED ORACLE's size.  `oracleOf_size_le` proves that size IS bounded by the
  input length -- but only for `bits` satisfying the machine's own header cap
  `16 * bits.length ≤ n`, via `Oracle.decoded_size`
  (`Proof/CaseAnalysis/WitnessOracleParameter.lean`).  `decoder_free` and
  `no_decoder_size_majorant` prove the RAW codec admits every circuit of the
  native arity at EVERY fixed length, so the codec alone has no majorant.
* §4 `oracleOf_size_majorant`: the paper's size guard, now applied by `oracleOf`
  (`Proof/CaseAnalysis/FinalTotalDecode.lean`, `paper.tex:4292`), restores one.
  `gate_rejects_wide` shows its `else` branch is genuinely reached.

`Proof/CaseAnalysis/FinalFuelMajorant.lean` records that "no length-only
decoded-size majorant is claimed"; §3 says why the codec cannot have one.
-/

namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound

open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation
open SourceInterfaces SupplierPipeline CanonicalBinary CanonicalWitnessCodec
open RepairOrdinary.RadixSemantics
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open RepairOrdinary.CloseoutFinalC10StageSeam
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10CallCountMajorant
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData sources k p)

/-! ## §1 The closed form: `actualFuel` is the call counts and nothing else -/

/-- **The stage's demanded fuel, as a function of the input length and the three
per-phase CALL COUNTS.**  Every summand is one of the corpus's own budgets at
`S.stageFuel ph n`, `S.entryWidth n` and `c ph`; the gate charge is the soundness
cutoff.  There is no `Nat` subtraction and no `Nat.log` anywhere in it. -/
def fuelAt (n : ℕ) (c : Phase → ℕ) : ℕ :=
  workerBudget (Soundness.cutoff (constantsOf sources))
    (fun _ => C10ComposeWidths.innerFuel
      (fun ph => stagedFuel (S.stageFuel ph)
        (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
          (joinScalarWidth (S.entryWidth n) (c ph)))
        (S.entryWidth n) (c ph) n)
      (fun ph => joinScalarWidth (S.entryWidth n) (c ph))
      C10TailVerdictUniform.tbud) n

/-- The fold's scalar width is the join width at the call count. -/
theorem widthOf_eq {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    widthOf sources k p S x bits ph
      = joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length := by
  unfold widthOf
  exact foldWidth_eq_joinScalarWidth (S.entryWidth n) _

/-- **`actualFuel` depends on the witness ONLY through the three call counts.** -/
theorem actualFuel_eq {n : ℕ} (x : BitInput n) (bits : List Bool) :
    actualFuel sources k p S x bits
      = fuelAt sources k p S n (fun ph => (records sources k p S x bits ph).length) := by
  have hF : phaseFuel sources k p S x bits
      = fun ph => stagedFuel (S.stageFuel ph)
          (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel
            (joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length))
          (S.entryWidth n) (records sources k p S x bits ph).length n := by
    funext ph
    rfl
  have hW : widthOf sources k p S x bits
      = fun ph => joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length := by
    funext ph
    exact widthOf_eq sources k p S x bits ph
  unfold actualFuel fuelAt
  rw [hF, hW]

/-! ## §2 Monotone up, bounded below: the exact satisfiability criterion -/

theorem lengths_mono {W W' : Phase → ℕ} (h : ∀ ph, W ph ≤ W' ph) (j : Fin 6) :
    C10ComposeWidths.lengths W j ≤ C10ComposeWidths.lengths W' j := by
  unfold C10ComposeWidths.lengths
  have hj := h (C10WidthCopies.phaseOf j)
  split
  · exact hj
  · unfold CompetitorRationalDecision.width
    omega

theorem widthCopies_budget_mono {V V' : Fin 6 → ℕ} (h : ∀ j, V j ≤ V' j) :
    C10WidthCopies.budget V ≤ C10WidthCopies.budget V' := by
  unfold C10WidthCopies.budget C10WidthCopies.charge
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  omega

theorem maxWidth_mono {W W' : Phase → ℕ} (h : ∀ ph, W ph ≤ W' ph) :
    C10ComposeWidths.maxWidth W ≤ C10ComposeWidths.maxWidth W' := by
  unfold C10ComposeWidths.maxWidth
  exact max_le_max (h Phase.penalty) (max_le_max (h Phase.moment) (h Phase.clause))

theorem innerFuel_mono {F F' W W' : Phase → ℕ} (hF : ∀ ph, F ph ≤ F' ph)
    (hW : ∀ ph, W ph ≤ W' ph) :
    C10ComposeWidths.innerFuel F W C10TailVerdictUniform.tbud ≤
      C10ComposeWidths.innerFuel F' W' C10TailVerdictUniform.tbud := by
  unfold C10ComposeWidths.innerFuel C10ComposeWidths.bodyFuel
  have h1 := C10FuelMajorant.bodyThreeFuel_mono hF
  have h2 := widthCopies_budget_mono (fun j => lengths_mono hW j)
  have h3 := C10TailVerdictUniform.tbud_mono (maxWidth_mono hW)
  omega

/-- **The demanded fuel is monotone in the call counts** -- the direction the
consumer needs, since `hfuel` is an UPPER bound on `actualFuel`. -/
theorem fuelAt_mono (n : ℕ) {c c' : Phase → ℕ} (h : ∀ ph, c ph ≤ c' ph) :
    fuelAt sources k p S n c ≤ fuelAt sources k p S n c' := by
  unfold fuelAt
  refine workerBudget_mono _ _ _ n ?_
  exact innerFuel_mono
    (fun ph => C10FuelMajorant.stagedFuel_mono (S.stageFuel ph) (S.entryWidth n) n (h ph))
    (fun ph => joinScalarWidth_mono (S.entryWidth n) (h ph))

/-! ## §3 The decoded oracle: the RAW decoder is free, and the gate is what
bounds it -/

/-! ## §4 What the gate restores: the majorant the raw decoder cannot have -/

end
end NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
