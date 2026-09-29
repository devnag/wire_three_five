import Proof.Wire_3_5.Primitive.Writers.C3WCostC3a

/-! # C3 request writer, part 19: sizes at a call

Output lengths within the steps (`wr_out_le`, `step_out_le`), C3a′'s input length (`c3aInput_len`), and the
flattened frames' lengths.

Paper quantity: none (size bookkeeping for the request writer's class bound, P3:3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.RepairOrdinary (frame frame_length)

/-- A tape blank at the start ends within the steps. -/
theorem step_out_le {t s n : ℕ} {p : Machine t s} {hi ho : Fin t → ℕ} {ti tf : Fin t → List Bool}
    (h : Step p n hi ti ho tf) (i : Fin t) (hh : hi i = 0) (ht : ti i = []) : (tf i).length ≤ n := by
  have := C3Mach.Wr5.steps_len h i 0 (by omega) (by rw [ht]; rfl)
  omega

/-- **A writer's output within its budget.** -/
theorem wr_out_le {t s : ℕ} {M : Machine t s} {B : ℕ} {i o : Fin t} {w v : List Bool} (hio : i ≠ o)
    (h : WriterIfaceJ.WriterRun M B i o w v) : v.length ≤ B := by
  obtain ⟨J, _, r, hr, hT, hH, hs⟩ := h
  have := RepairOrdinary.DecompositionSource.one_tape_support M B ⟨M.start, fun _ => 0, WriterIface.inBank i w⟩ r o 0
    hr (le_refl _) (by simp [WriterIface.inBank, Ne.symm hio])
  rw [hT] at this
  have e := WriterIfaceJ.outBankJ_out i o hio w v J
  rw [e] at this
  omega

theorem flatMap_frame_len (l : List (List Bool)) : l.length ≤ (l.flatMap frame).length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons]; omega

theorem flatMap_frame_len' {α : Type} (l : List α) (f : α → List Bool) :
    l.length ≤ (l.flatMap fun x => frame (f x)).length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons]; omega

theorem loadRec_len (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    (Top.loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10).length = 2 * (f0.length + f1.length + f2.length + f3.length +
      f4.length + f5.length + f6.length + f7.length + f8.length + f9.length + f10.length) + 11 := by
  simp only [Top.loadRec, List.length_append, frame_length]; omega

theorem sum_len_le (atoms : List (List (List Bool))) :
    (atoms.map List.length).sum ≤ (C3Asm.atomsStream atoms).length := by
  induction atoms with
  | nil => simp [C3Asm.atomsStream]
  | cons E atoms ih =>
    have h1 := flatMap_frame_len E
    simp only [C3Asm.atomsStream, List.flatMap_cons, List.map_cons, List.sum_cons, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢
    omega

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
