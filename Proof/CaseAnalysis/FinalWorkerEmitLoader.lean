import Proof.CaseAnalysis.FinalWorkerEmitShape

/-! # W2 -- the emit loader, built

Paper C.10.1 (paper.tex 4130):

> In addition to validity, the machine estimates `mu = E_{i,u} F_i(u)` **by
> expanding it into AND-four supplier calls**, and accepts a branch only if
> `mu~ >= theta_acc := (c_p + s_p)/2`.

`RepairCloseoutFinalC10WorkerDockBody.body_runs` leaves the emitter's operand
ports open.  `RepairCloseoutFinalC10WorkerEmitShape` fixed the SHAPE of that
obligation (`EmitEntry`); this module DISCHARGES it with one concrete machine.

## The one width change, and the corpus stage that performs it

`CompetitorSumFold.Store` carries the fold's accumulator as
`ZeroPadding.pad (capacity b) (frame (binary (width b) a.positive))` on bank
tape `92`, the same for the negative numerator on `93`, and
`ZeroPadding.pad (capacity b) (frame (binary b a.denominator))` on `96`.
`CloseoutRowsEstimatorCoefficients.Append.input` wants all three at the WIDE
width: `frame (binary (width b) …)`, unpadded.  The denominator therefore has
to change field width, and `ZeroPadding.pad` cannot bridge that because `frame`
interleaves markers.

The corpus already has the stage: `ClockNormalize.machine` reads a unary width
driver and a framed source and emits the source re-encoded at the driver's
width (`ClockScalarFields.scalar_run`: tape `2` becomes
`frame (binary w (value bits))`, and **every head returns to zero**).  With
`SignedSortKey.binary_value` this is exactly the field-width change, and with
the driver at the fold's own wide width word (`Store.wideWidth`, bank tape
`98`) it is also, for the two numerators, the unpadding copy.  So all three
data ports are one and the same stage, run three times.

`Step.pad` is what lets the stage read the fold's PADDED tapes: padding every
tape with blanks is invisible to a local machine, so the same receipt applies
at `ZeroPadding.pad (capacity b) …`.  The stage's two scratch tapes must start
blank-padded, and the fold's own reset tapes are exactly that
(`Store.loaderReset`, `Store.eraseReset`, `Store.copyCounter`,
`Store.copyReset` are `List.replicate (capacity b) false`); the counter tape is
returned to its blank state by the stage itself, so one counter serves all
three calls and the three flag tapes are the three remaining resets.

Bank tapes used, all frozen: driver `98`, sources `92`, `93`, `96`, outputs
`210`, `211`, `212` (`= answerSlot 23, 24, 25`), flags `181`, `184`, `185`,
counter `183`.  Nothing outside the fold's own bank is touched, and the
emitter's constant ports `187`, `213`, `214` are the loader's.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_value)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The three slot maps -/

/-- The positive numerator's re-encoding: driver `98`, source `92`, output
`210 = answerSlot 23`, flag `181`, counter `183`. -/
def slotsP : Fin 5 → Fin 218 := ![98, 92, 210, 181, 183]

/-- The negative numerator's re-encoding: flag `184`, same counter. -/
def slotsN : Fin 5 → Fin 218 := ![98, 93, 211, 184, 183]

/-- The denominator's WIDTH CHANGE: source `96` carries `binary b d`, the
driver `98` carries the wide width, so the output is `binary (width b) d`. -/
def slotsD : Fin 5 → Fin 218 := ![98, 96, 212, 185, 183]



/-! ## §2 One re-encoding stage, docked -/


/-! ## §3 The emit loader -/

noncomputable def stage (slots : Fin 5 → Fin 218) : Machine 218 6 :=
  RecoveryFocus.machine slots ClockNormalize.machine

/-- **The emit loader.**  Three runs of the corpus's width normalizer, on the
fold's own bank, at three fixed slot maps.  It is ONE machine: it does not
depend on the record width, on the call count, on the phase, or on the witness
-- the widths it works at are read off the fold's own dimension words. -/
noncomputable def emitLoader :=
  Composition.machine (Composition.machine (stage slotsP) (stage slotsN)) (stage slotsD)

/-- The emit loader's fuel: three copies of the normalizer's own budget at the
wide scalar width, plus the two paid bridge steps.  No summand mentions the
witness. -/
def emitFuel (b : ℕ) : ℕ :=
  (4 * CompetitorRationalDecision.width b + 4) + 1 +
    (4 * CompetitorRationalDecision.width b + 4) + 1 +
    (4 * CompetitorRationalDecision.width b + 4)

/-! ## §4 The head invariant -/


/-! ## §5 The fold's stored fields, as bank ports -/

/-! ## §6 The emit loader's receipt -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
