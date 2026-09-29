import Proof.Packets.PacketsNatSum

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.PacketsGlue.NatAt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue

namespace One

/-! ## The decoder: NatSum's item states, halting after one item -/

/-! ## One transition each -/

section Steps

end Steps

section Loops

end Loops

section WLoops

end WLoops

/-! ## One bit, then all bits -/

/-! ## One natWord, then the list -/

end One

/-! ## The skipper: NatSum's header states, halting at 4 -/

namespace Skip

/-! ## One transition each -/

section Steps

end Steps

section Loops

end Loops

end Skip

/-! ## `k` skips, then one decode -/

/-- A timed run that ends halted, from the start state, is a `Step`. -/
theorem Timed.toStep {t s n : ℕ} {p : Machine t s} {c d : Configuration t s} (h : Timed p n c d)
    (hd : p.halted d.control = true) (hc : c.control = p.start) :
    Step p n c.heads c.tapes d.heads d.tapes := by
  obtain ⟨r, hr, hf, _⟩ := h.run hd
  obtain ⟨q, H, A⟩ := c
  simp only at hc
  subst hc
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

end NearCubicWires.PacketsGlue.NatAt

