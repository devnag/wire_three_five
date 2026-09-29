import Proof.Wire_3_5.Lists.ListMachinePrintCore

/-! # C2p, the record printer: a support bitmap as a monomial record (P3:1482-1488)

Realizes the output step of the interpolation printer: for the support bitmap `X` of a printed monomial, the record
`recW (supp X) = true :: frame (monoBits (supp X))` (the M5 tape encoding, the input format) is appended at the
output cursor. The coordinates are printed in unary, `atomCode i = 1^i 0`, from a unary position word `frame (1^i)`
that grows by one position per bit of `X` (`UExtend`) and is copied, as pairs, at each one of `X` (`CopyOpen`).

The paper quantity is the printed record. Results: `armT_step`/`armF_step` (one position), `br_step` (the branch on
the bit), `body_step`, `loop_run` (the positions of `X`), and **`rec_run`**: `recW (supp X)` appended, the bitmap, the
position word and the logs unchanged, every head but the output's back at `0`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Print
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.WireExponent3_5.ListMachine.Interp (supp)
open NearCubicWires.WireExponent3_5.ListMachine.Rec (atomCode monoBits recW dockRun maskRun)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-! ## Reading a framed word -/

theorem frame_read (xs : List Bool) : ∀ i (hi : i < xs.length),
    readTapeBit (frame xs) (2 * i) = true ∧ readTapeBit (frame xs) (2 * i + 1) = xs[i] := by
  induction xs with
  | nil => intro i hi; simp at hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero => simp [readTapeBit, frame]
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [readTapeBit, frame, Nat.mul_succ, List.getD_cons_succ] using this

theorem frame_read_end (xs : List Bool) : readTapeBit (frame xs) (2 * xs.length) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [readTapeBit, frame, Nat.mul_succ, List.getD_cons_succ] using ih

/-! ## The output of one position -/

theorem marks_flatMap (S : List ℕ) (f : ℕ → List Bool) :
    Streaming.marks (S.flatMap f) = S.flatMap fun p => Streaming.marks (f p) := by
  induction S with
  | nil => rfl
  | cons a S ih => simp [List.flatMap_cons, Streaming.marks_append, ih]

/-! ## One position: the arms of the branch (tapes: 0 the bitmap, 1 the position word, 2 the output) -/

def slUO : Fin 2 → Fin 3 := ![1, 2]
def slO3 : Fin 1 → Fin 3 := ![2]
def slU3 : Fin 1 → Fin 3 := ![1]

theorem slUO_inj : Function.Injective slUO := by decide
theorem slO3_inj : Function.Injective slO3 := by decide
theorem slU3_inj : Function.Injective slU3 := by decide

theorem dockH_UO (H : Fin 3 → ℕ) (v : Fin 2 → ℕ) : dockH slUO H v = ![H 0, v 0, v 1] := by
  funext i; fin_cases i
  · exact dockH_other slUO H v 0 (by decide)
  · exact dockH_slot slUO slUO_inj H v 0
  · exact dockH_slot slUO slUO_inj H v 1

theorem install_UO (A : Fin 3 → List Bool) (v : Fin 2 → List Bool) :
    RecoveryRootRound.install slUO A v = ![A 0, v 0, v 1] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slUO A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slUO slUO_inj A v 0
  · exact RecoveryRootRound.install_slot slUO slUO_inj A v 1

theorem dockH_O3 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) : dockH slO3 H v = ![H 0, H 1, v 0] := by
  funext i; fin_cases i
  · exact dockH_other slO3 H v 0 (by decide)
  · exact dockH_other slO3 H v 1 (by decide)
  · exact dockH_slot slO3 slO3_inj H v 0

theorem install_O3 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slO3 A v = ![A 0, A 1, v 0] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slO3 A v 0 (by decide)
  · exact RecoveryRootRound.install_other slO3 A v 1 (by decide)
  · exact RecoveryRootRound.install_slot slO3 slO3_inj A v 0

theorem dockH_U3 (H : Fin 3 → ℕ) (v : Fin 1 → ℕ) : dockH slU3 H v = ![H 0, v 0, H 2] := by
  funext i; fin_cases i
  · exact dockH_other slU3 H v 0 (by decide)
  · exact dockH_slot slU3 slU3_inj H v 0
  · exact dockH_other slU3 H v 2 (by decide)

theorem install_U3 (A : Fin 3 → List Bool) (v : Fin 1 → List Bool) :
    RecoveryRootRound.install slU3 A v = ![A 0, v 0, A 2] := by
  funext i; fin_cases i
  · exact RecoveryRootRound.install_other slU3 A v 0 (by decide)
  · exact RecoveryRootRound.install_slot slU3 slU3_inj A v 0
  · exact RecoveryRootRound.install_other slU3 A v 2 (by decide)

/-! ## The branch on the bit, with the position word rewound -/

/-! ## The positions of the bitmap (tapes: 0 the bitmap, 1 the position word, 2 the output, 3 the word's log) -/


/-! ## The record -/



theorem frame_eq_marks (x : List Bool) : frame x = Streaming.marks x ++ [false] := by
  have := Streaming.frame_append x []
  simpa [frame] using this

theorem recW_eq (S : List ℕ) : recW S = true :: (Streaming.marks (monoBits S) ++ [false]) := by
  rw [recW, frame_eq_marks]


end NearCubicWires.WireExponent3_5.ListMachine.Print
