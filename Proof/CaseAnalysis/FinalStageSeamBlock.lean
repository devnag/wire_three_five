import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalTailCompose

/-! # S2 -- the stage seam, as T3's `BlockRuns`

Paper C.10 (paper.tex 4098-4110):

> The weak machine estimates `E_{i,j,u} P_ij` and every `E_u Q_ij`.

T3's composition (`RepairCloseoutFinalC10TailCompose.BlockRuns`) consumes each
phase block as one run from the parked bank `entryOf (wflag e) input witness`
that leaves the record word on `wport e` AND leaves the verifier's input tape
`winput e` and witness tape `wwit e` as received: the three blocks share tapes
`0` and `1`, and no `len`-determined budget can copy them.

The docked body never writes tapes `0` and `1`: every one of its stages is a
`RecoveryFocus.machine` at a slot map whose values are all `≥ 2`
(`entrySlot j = 2 + j`, `foldSlot j ∈ {76, 92 + j}`, `answerSlot j = 187 + j`,
`slotsP/N/D ⊆ {92, 93, 96, 98, 181, 183, 184, 185, 210, 211, 212}`), so the
corpus's own rule-table invariant `RecoveryTseitinReadOnly.NoWrite` -- closed
under `Composition.machine` (`composition`) and discharged for an unselected
slot (`unselected`) -- gives, through `run_tape`, that the exit agrees with the
entry on those two tapes.  Nothing about the stages' semantics is re-proved.

* `docked_run_frame` is `docked_run` plus `exit 0 = bank 0 ∧ exit 1 = bank 1`.
* `entryOf_addCases` machine-checks T3's `entryOf` against
  `stageInput_addCases`: the parked bank on `218 + e` tapes is the 218-tape
  parked bank with every extra tape blank.
* `blockRuns_of_stage` is T3's `BlockRuns` for `stagedBody stage emitLoader`,
  from the stage receipt `hstage` (as in `estimatorBody_of_stage`) plus the
  stage contract that it hands tapes `0` and `1` through unchanged
  (`h0 : bank 0 = frame (List.ofFn x)`, `h1 : bank 1 = frame bits`).

No constant is chosen here.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeamBlock

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
  (BlockRuns entryOf entry_eq wflag wport winput wwit wflag_val)
open NearCubicWires.RepairSource.RecoveryTseitinReadOnly (NoWrite)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The docked body never writes tapes `0` and `1` -/

/-! ## §2 The dock without its loader, framing tapes `0` and `1` -/

/-! ## §3 T3's parked bank, against the seam's layout -/

/-! ## §4 The seam, as a block -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeamBlock
