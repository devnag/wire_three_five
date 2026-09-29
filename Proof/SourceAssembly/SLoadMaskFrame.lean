import Proof.SourceAssembly.SLoadCore

/-! Framing the mask worker's output.

`MaskProducer.correct` promises only the bare `q`-bit word on tape 4 of an
arbitrary compatible final bank; `Request.input` needs it framed. This module
pays for that with the existing raw framer `AppendFrameKernel.machine`, driven
by a retained unary domain word, writing onto a zero-backed scratch slot. No
private tape of the mask worker is read, and the mask slot itself is left
exactly as the callee returned it. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.MaskFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
noncomputable section

/-- A `ClockJoin.ReadyRun` receipt is a `Step` receipt. -/
theorem step_of_clockReady {t s n : Nat} {p : Machine t s} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p n input output) :
    Step p n (fun _ => 0) input (fun _ => 0) output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  refine ⟨r, ?_, funext hh, ht, hs⟩
  change runFrom p n (initialConfiguration p input) = some r at hr
  exact hr

theorem quad_injective {u : Nat} (a b c d : Fin u) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → Fin u) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | rfl
      | (exact absurd hij hab) | (exact absurd hij.symm hab)
      | (exact absurd hij hac) | (exact absurd hij.symm hac)
      | (exact absurd hij had) | (exact absurd hij.symm had)
      | (exact absurd hij hbc) | (exact absurd hij.symm hbc)
      | (exact absurd hij hbd) | (exact absurd hij.symm hbd)
      | (exact absurd hij hcd) | (exact absurd hij.symm hcd)


end
end SLoad.MaskFrame
