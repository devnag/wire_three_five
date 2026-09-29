import Proof.CaseAnalysis.FinalWorkerDockBody

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape

open Finset
open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockBody
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerJoin
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 A local run never shortens a tape -/

/-! ## §2 The answer slots are outside both docked stages -/

/-! ## §3 The premise really is satisfiable -/

/-! ## §4 The current `hemit` is refutable -/

/-! ## §5 The corrected premise -/

/-- The emitter's `n`-determined constant ports: the runtime width word and the
two normalization fields.  These are the loader's, not the emit loader's: they
name no fold output. -/
def emitConstants (b : ℕ) (j : Fin 29) : List Bool :=
  if j.val = 0 then List.replicate b true
  else if j.val = 26 ∨ j.val = 27 then frame (binary b 1) else []

/-- **What the loader must leave on bank tapes `187 .. 215`.**  The three data
ports `23, 24, 25` are empty -- the emit loader writes them from the fold's
stored accumulator -- and the constant ports carry their words. -/
def EmitEntry (b : ℕ) (bank : Fin 218 → List Bool) : Prop :=
  ∀ j : Fin 29,
    bank (answerSlot j) = if j.val = 23 ∨ j.val = 24 ∨ j.val = 25 then [] else emitConstants b j

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
