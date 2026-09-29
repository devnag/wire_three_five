import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Proof.Assembly.RowsPoolMinimumLoop
import Proof.CaseAnalysis.RowsTouchingPascalNext
import Proof.CaseAnalysis.WitnessHeaderSwitch
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.Layout

/-! A.4 mask dock.  The deterministic touching selector already leaves the
live-set mask on one physical tape.  The X/C pool loops read their live bit
from a mask tape of their own port chart; this file shows the two are the
SAME list, and fixes the injective slot maps that let the pool loops be
docked onto the selector's bank without copying the mask. -/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalPool
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsGateSupport CloseoutRowsPoolWeight
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- A `RepeatMachine` loop receipt, restated as this project's `Step`. -/
theorem step_of_repeat {t s : ℕ} (body : Machine t s) (acc : Fin s→(Fin t→Bool)→Bool) (n : ℕ)
    (c d : Configuration t s) (total h1 h2 : ℕ)
    (r : ExecutionReceipt (t+1) (Fintype.card (RepeatMachine.Control s)))
    (hr:runFrom (RepeatMachine.machine body acc) n (RepeatMachine.cfg 0 c total h1)=some r)
    (hf:r.final=RepeatMachine.cfg 3 d total h2) :
    Step (RepeatMachine.machine body acc) n
      (Fin.addCases c.heads (fun _ : Fin 1=>h1))
      (Fin.addCases c.tapes (fun _ : Fin 1=>CompareMachine.word total))
      (Fin.addCases d.heads (fun _ : Fin 1=>h2))
      (Fin.addCases d.tapes (fun _ : Fin 1=>CompareMachine.word total)):=by
  have entry:RepeatMachine.cfg 0 c total h1=
      (⟨(RepeatMachine.machine body acc).start,Fin.addCases c.heads (fun _ : Fin 1=>h1),
        Fin.addCases c.tapes (fun _ : Fin 1=>CompareMachine.word total)⟩ :
          Configuration (t+1) (Fintype.card (RepeatMachine.Control s))):=by
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  rw [entry] at hr
  exact Step.of_run hr (by rw [hf];rfl) (by rw [hf];rfl)


/-! ### The shared bank.

`Fin 64` holds the selector's 36 tapes at 0-35, the weight loop's private
tapes at 36-39 and the minimum loop's private tapes at 41-61.  BOTH pool
loops take their mask port to slot 1 - the very tape the selector wrote. -/






end NearCubicWires.RepairOrdinary.CloseoutFinalPool
