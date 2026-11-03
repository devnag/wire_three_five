import Proof.CaseAnalysis.FinalWorkerDock

/-! # W2 -- the answer emitter, and the `EstimatorBody` junction closed to two loaders

Paper C.10.1 (paper.tex 4130):

> In addition to validity, the machine estimates `mu = E_{i,u} F_i(u)` **by
> expanding it into AND-four supplier calls**, and accepts a branch only if
> `mu~ >= theta_acc := (c_p + s_p)/2`.

`RepairCloseoutFinalC10WorkerDock` docked the multiply stage and the cold fold
into one bank and proved one `Step` of the composed machine whose exit bank
carries the exact signed-rational fold of the AND-four call stream.  What
`Realizes.hencoded` additionally demands is that the phase's output PORT carry
the corpus's own record word for that fold.  This module docks the answer
emitter (`CompetitorCountRecordAppend`, `Fin 29`) at bank tapes `187 .. 215`,
with `port = 215` its output tape, and assembles the whole `EstimatorBody`.

## The two loaders, and why they are hypotheses and not assumptions

P4's `gated_verifier_pass` hands the body the verifier's own tapes: all heads
at zero, tape `0` the framed input, tape `1` the framed witness, the single
scratch slot `flag` carrying `[true]`, and every other tape blank.  Two things
have to be written onto the bank before the corpus's stages can run, and
neither is a blank tape (f32 §V.8: `List.replicate C false` is NOT discharged
by `[]`, and a stage that READS a tape is not one that leaves it untouched):

* `loader` -- the stage dimension words and S1's call-record stream, at the
  multiply stage's and the fold's own input ports.  Stated as `DockReady`.
* `emitLoader` -- the emitter's five operand ports, at the emitter's field
  widths, read off the fold's stored accumulator.  Stated as an explicit
  quantified `Step` over the fold's exit, so it cannot be met by a stage that
  ignores what the fold computed: its premise is the fold's own `Store`, and
  its conclusion names `CompetitorSumFold.folded` of the call stream.

Both are `n`-determined: their inputs are the record width, the CALL COUNT and
the fold's stored fields, never the witness length.  The one arithmetic fact
they have to supply that no existing corpus stage provides is the field-width
change on the denominator: `CompetitorSumFold.Store` carries
`binary b a.denominator` on bank tape `96` while
`CloseoutRowsEstimatorCoefficients.Stream.recordFields` wants
`binary (CompetitorRationalDecision.width b) a.denominator`, and
`ZeroPadding.pad` cannot bridge that because `frame` interleaves markers.  That
is the residual, named exactly.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The emitter's slots -/

theorem answerSlot_val (j : Fin 29) : (answerSlot j).val = 187 + j.val := rfl

theorem answerSlot_injective : Function.Injective answerSlot := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [answerSlot_val, answerSlot_val] at hv
  exact Fin.ext (by omega)

theorem port_eq : port = answerSlot 28 := rfl

/-- **The emitter is docked, and its output port carries the record word.**
One real execution of the corpus's record appender, docked at bank tapes
`187 .. 215`, from a bank that carries its five operand ports.  Its cost
depends only on the scalar width. -/
theorem answer_step (scalarWidth : ℕ) (estimate : CompetitorValidity.Estimate)
    (heads : Fin 218 → ℕ) (bank : Fin 218 → List Bool)
    (hheads : ∀ j : Fin 29, heads (answerSlot j) = 0)
    (hbank : ∀ j : Fin 29,
      bank (answerSlot j) =
        CloseoutRowsEstimatorCoefficients.Append.input scalarWidth estimate 1 1 j) :
    ∃ (exitHeads : Fin 218 → ℕ) (exit : Fin 218 → List Bool),
      Step (RecoveryFocus.machine answerSlot CompetitorCountRecordAppend.machine)
        (CompetitorCountRecordAppend.budget scalarWidth) heads bank exitHeads exit ∧
      exit port =
        CloseoutRowsEstimatorCoefficients.Stream.recordWord scalarWidth estimate 1 1 := by
  obtain ⟨receipt, hrun, _hsteps, hword⟩ := result_record_run scalarWidth estimate
  have hstep :
      Step CompetitorCountRecordAppend.machine
        (CompetitorCountRecordAppend.budget scalarWidth) (fun _ => 0)
        (CloseoutRowsEstimatorCoefficients.Append.input scalarWidth estimate 1 1)
        receipt.final.heads receipt.final.tapes :=
    Step.of_run hrun rfl rfl
  have hdock := hstep.dock answerSlot answerSlot_injective heads bank hheads hbank
  refine ⟨dockH answerSlot heads receipt.final.heads,
    install answerSlot bank receipt.final.tapes, hdock, ?_⟩
  rw [port_eq, install_slot answerSlot answerSlot_injective bank receipt.final.tapes 28]
  exact hword

/-! ## §2 The whole estimator body -/

/-! ## §3 The body's run, as one Prop -/

/-- Every contribution of the call stream is valid at the fold's scalar width. -/
theorem contributions_valid (entryWidth : ℕ) (entries : List Entry)
    (hentries : ∀ entry ∈ entries,
      CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid entryWidth entry) :
    ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate
        (CompetitorRationalDecision.width entryWidth) := by
  intro estimate hestimate
  rcases List.mem_map.mp hestimate with ⟨entry, hentry, rfl⟩
  exact CloseoutRowsEstimatorCoefficients.Stream.Entry.valid_estimate entryWidth entry
    (hentries entry hentry)

/-! ## §4 The junction, closed -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
