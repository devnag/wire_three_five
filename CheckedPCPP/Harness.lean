import Proof.Foundations.OrdinaryRewindCarrier
import Proof.MachineModel.ClockJoin
import Bindings.TuringBridge.Budget

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-- A rewound word function is a `ReadyRun` from its framed input to its output. -/
theorem wordFunction_ready {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) :
    ∃ out, ClockJoin.ReadyRun (Rewind.program f.program).machine (2 * budget req + 2)
      ((Rewind.program f.program).inputTapes (input req)) out ∧
      out (Rewind.program f.program).outputTape = output req := by
  obtain ⟨r, hr, hout, hh⟩ := WordFunction.reset_realizes f req
  refine ⟨r.final.tapes, ⟨r, hr, rfl, hh, ?_⟩, hout⟩
  exact runFrom_steps_le _ _ _ r hr

/-- The input bank of a program: the framed word on tape 0, every other tape empty. -/
theorem program_inputTapes (p : Program) (word : List Bool) (i : Fin p.tapeCount) :
    p.inputTapes word i = if i.val = 0 then frame word else [] := rfl

end NearCubicGates.Close.CheckedPCPP
