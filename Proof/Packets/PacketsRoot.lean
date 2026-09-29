import Proof.Packets.PacketsGlueMetaMul
import Proof.Packets.PacketsNatAt

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsGlue.CeilSqrt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.CanonicalFourfoldRowProgram

/-- The counter: a sentinel, then `c` ones. -/
def sentC (c : ℕ) : List Bool := false :: List.replicate c true

section Steps

end Steps

/-! ## Tape facts -/

theorem read_rep (x i : ℕ) : readTapeBit (List.replicate x true) i = decide (i < x) := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < x
  · simp [h]
  · simp [h]

theorem read_sent (c i : ℕ) : readTapeBit (sentC c) i = decide (1 ≤ i ∧ i ≤ c) := by
  cases i with
  | zero => rfl
  | succ i =>
    unfold sentC readTapeBit
    simp only [List.getD_cons_succ]
    have := read_rep c i
    unfold readTapeBit at this
    rw [this]
    simp

theorem write_rep (c : ℕ) : writeTapeBit (List.replicate c true) c true = List.replicate (c + 1) true := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [List.replicate_succ, List.replicate_succ]
    simp only [writeTapeBit, ih]

theorem write_sent (c : ℕ) : writeTapeBit (sentC c) (c + 1) true = sentC (c + 1) := by
  unfold sentC
  simp only [writeTapeBit, write_rep]

/-! ## Loops -/

end NearCubicWires.PacketsGlue.CeilSqrt

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.CanonicalFourfoldRowProgram
noncomputable section

end
end NearCubicWires.PacketsGlue.RequestMeta

