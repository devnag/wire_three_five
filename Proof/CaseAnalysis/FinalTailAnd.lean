import Proof.CaseAnalysis.FinalLengthGate
import Proof.CaseAnalysis.FinalSelectorCellSetter

/-! **Decision tail, stage 2b-iii(a) — the AND of the three verdicts.**

Paper C.10: the machine passes validity only if BOTH validity tests hold, and
accepts only if the acceptance test holds as well. Three flags, one result bit.
No AND accumulator is needed: P4's `branch` is a two-way test on a flag that
rejects (writes `false` on `result`, halts) or continues, so three nested
branches ending in `setOne` (writes `true`) compute exactly `f1 ∧ f2 ∧ f3`. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailAnd

open NearCubicWires.RepairOrdinary
open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairOrdinary.CloseoutFinalSelector
open NearCubicWires.RepairOrdinary.RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- `setOne` docked on a single slot. -/
noncomputable def setSlot {u : ℕ} (res : Fin u) : Machine u 2 :=
  RecoveryFocus.machine (fun _ : Fin 1 => res) setOne

/-- Innermost: test `f3`, then commit. -/
noncomputable def and1 {u : ℕ} (f3 res : Fin u) : Machine u (2 + 2) := branch f3 res (setSlot res)
/-- Then `f2`. -/
noncomputable def and2 {u : ℕ} (f2 f3 res : Fin u) : Machine u (2 + (2 + 2)) :=
  branch f2 res (and1 f3 res)
/-- Three verdict flags in series, then commit `true`. -/
noncomputable def and3 {u : ℕ} (f1 f2 f3 res : Fin u) : Machine u (2 + (2 + (2 + 2))) :=
  branch f1 res (and2 f2 f3 res)

/-- Docking `setOne` on one slot is `Function.update` at that slot. -/
theorem install_single {u : ℕ} (res : Fin u) (A : Fin u → List Bool) (v : List Bool) :
    install (fun _ : Fin 1 => res) A (fun _ => v) = Function.update A res v := by
  funext i
  by_cases h : i = res
  · subst h
    rw [Function.update_self]
    exact install_slot (fun _ : Fin 1 => i) (fun a b _ => Fin.ext (by omega)) A (fun _ => v) 0
  · rw [Function.update_of_ne h]
    exact install_other (fun _ : Fin 1 => res) A (fun _ => v) i (fun _ => Ne.symm h)

theorem setSlot_step {u : ℕ} (res : Fin u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : H res = 0) (hA : A res = [false]) :
    Step (setSlot res) 1 H A H (Function.update A res [true]) := by
  have hs : Step setOne 1 (fun _ => 0) (fun _ => [false]) (fun _ => 0) (fun _ => [true]) :=
    Step.of_ready (set_ready false)
  have hd := hs.dock (fun _ : Fin 1 => res) (fun a b _ => Fin.ext (by omega)) H A
    (by intro j; simp [hH]) (by intro j; simp [hA])
  rw [dockH_existing _ H (fun _ => 0) (by intro j; simp [hH]), install_single] at hd
  exact hd

/-- Rejecting on `res = [false]` at head `0` changes nothing. -/
theorem exitTapes_false_self {u : ℕ} (res : Fin u) (A : Fin u → List Bool)
    (hA : A res = [false]) : exitTapes res A 0 false = A := by
  funext i
  unfold exitTapes
  by_cases h : i = res
  · subst h; simp [hA, writeTapeBit]
  · simp [h]

end NearCubicWires.RepairSource.CloseoutFinal.C10TailAnd
