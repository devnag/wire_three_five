import Proof.MachineModel.BlockPlatform

/-! # A machine stated as `Step`s, delivered as a `WordFunction`.

`RepairCloseoutFinalC10WordFunctionDock` already carries the direction
*word function → `Step`* (`step_of_realizes`, `step_of_rewound`,
`rewound_bank_dock`, `wordFunction_bank_dock`). Nothing carried the reverse,
so every `WordFunction` in the corpus — `RepairEquationRowProducer.producer`,
`RepairOrdinaryRankCarrier.carrier`, `RepairOrdinaryMemoryChecker.carrier` —
is hand-built from its own run lemma, while the whole batch layer speaks
`Step`. This module closes that gap once.

The consumer is `PacketWriter.ordinary`, whose type is
`RewoundWordFunction Request (Request.input a) (Request.raw selector a)
(packetBudget a coefficient degree)`. That budget is fixed by the consumer, so
routing through `WordFunction.reset` — which charges `2 * budget + 2` for
returning the heads to zero — would cost coefficient/degree slack. A machine
that already ends with every head at `0`, which is what `masked` and
`Cells.run` deliver, must therefore reach `RewoundWordFunction` at its own
budget. `toRewound` is exactly that statement.

The proof is one unfolding. `run p n T` is `runFrom p n (initialConfiguration p T)`
and `initialConfiguration p T` is `⟨p.start, fun _ => 0, T⟩`, which is the
configuration `Step p n (fun _ => 0) T _ _` starts from; `runFrom` is a
function, so the receipt a caller is handed is the receipt the `Step` already
names. No new machine, no semantics, no induction.
-/
namespace NearCubicWires.BlockPlatform
open LocalBitMultitape RepairOrdinary NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}

structure WordBlocks (Request : Type) (input output : Request → List Bool)
    (budget : Request → ℕ) where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFresh : outputTape.val ≠ 0
  cost : Request → ℕ
  exitH : Request → Fin tapeCount → ℕ
  exitA : Request → Fin tapeCount → List Bool
  step : ∀ r, Step machine (cost r) (fun _ => 0)
    (fun i => if i.val = 0 then frame (input r) else []) (exitH r) (exitA r)
  exitOut : ∀ r, exitA r outputTape = output r
  fits : ∀ r, cost r ≤ budget r

/-- The program a `WordFunction` is built on: the shared machine, its output
tape, and the two side conditions `Program` demands. -/
def WordBlocks.program (W : WordBlocks Request input output budget) : Program :=
  ⟨W.tapeCount, W.stateCount, W.twoTapes, W.machine, W.outputTape, W.outputFresh⟩

@[simp] theorem WordBlocks.program_machine (W : WordBlocks Request input output budget) :
    W.program.machine = W.machine := rfl

@[simp] theorem WordBlocks.program_outputTape (W : WordBlocks Request input output budget) :
    W.program.outputTape = W.outputTape := rfl

/-- The receipt `step` names, at the consumer's budget rather than the block's
own cost. `Step.enlarge` keeps the SAME receipt (`runFrom_moreFuel`), so the
exit heads and tapes below are the block's, unchanged. -/
theorem WordBlocks.receipt (W : WordBlocks Request input output budget) (r : Request) :
    ∃ rec : ExecutionReceipt W.tapeCount W.stateCount,
      run W.program.machine (budget r) (W.program.inputTapes (input r)) = some rec ∧
        rec.final.heads = W.exitH r ∧ rec.final.tapes = W.exitA r := by
  obtain ⟨rec, hrun, hh, ht, _⟩ := (W.step r).enlarge (W.fits r)
  exact ⟨rec, hrun, hh, ht⟩

theorem WordBlocks.realizes (W : WordBlocks Request input output budget) (r : Request) :
    ∃ rec, run W.program.machine (budget r) (W.program.inputTapes (input r)) = some rec ∧
      rec.final.tapes W.program.outputTape = output r := by
  obtain ⟨rec, hrun, _, ht⟩ := W.receipt r
  refine ⟨rec, hrun, ?_⟩
  rw [WordBlocks.program_outputTape, ht]
  exact W.exitOut r

/-- A `Block` family over one machine is a word function at its own budget. -/
def WordBlocks.toWordFunction (W : WordBlocks Request input output budget) :
    WordFunction Request input output budget :=
  ⟨W.program, W.realizes⟩

@[simp] theorem WordBlocks.toWordFunction_program (W : WordBlocks Request input output budget) :
    W.toWordFunction.program = W.program := rfl

/-- Every receipt a caller can obtain is the one `step` names: `runFrom` is a
function, so `some rec = some receipt` forces `rec = receipt`. This is why no
execution is repeated here. -/
theorem WordBlocks.headsReset (W : WordBlocks Request input output budget)
    (hz : ∀ r, W.exitH r = fun _ => 0) (r : Request) (receipt : _)
    (hreceipt : run W.program.machine (budget r) (W.program.inputTapes (input r)) = some receipt) :
    ∀ tape, receipt.final.heads tape = 0 := by
  obtain ⟨rec, hrun, hh, _⟩ := W.receipt r
  have hrec : rec = receipt := Option.some.inj (hrun.symm.trans hreceipt)
  intro tape
  -- Pointwise, because `receipt` is typed at `W.program.tapeCount` and `rec` at
  -- `W.tapeCount`: defeq, but not syntactically equal, so a function-level
  
  have hpt : receipt.final.heads tape = W.exitH r tape := by
    rw [← hrec]
    exact congrFun hh tape
  have hzero : W.exitH r tape = 0 := by rw [hz r]
  exact hpt.trans hzero

/-- **The consumer's type.** When every block also exits with all heads at `0`
— which `masked` (`BlockLoop.masked`) and `Cells.run` both give — the machine
is a `RewoundWordFunction` at the SAME budget. No `reset`, no `2 * budget + 2`. -/
def WordBlocks.toRewound (W : WordBlocks Request input output budget)
    (hz : ∀ r, W.exitH r = fun _ => 0) :
    RewoundWordFunction Request input output budget :=
  { W.toWordFunction with headsReset := fun r receipt h => W.headsReset hz r receipt h }

@[simp] theorem WordBlocks.toRewound_program (W : WordBlocks Request input output budget)
    (hz : ∀ r, W.exitH r = fun _ => 0) : (W.toRewound hz).program = W.program := rfl

end
end NearCubicWires.BlockPlatform
