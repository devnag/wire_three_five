import Proof.Wire_3_5.FinalPass.Core5

/-! # S5Core, part 6: one writer's stage on the bank (P3:3170-3181)

A writer (a machine on its encoded bank, `CoreWordsM` / `SymWordsM`) runs on the bank with its input stream on the
bank's input tape, its outputs on the output tapes, everything else on its own fresh block of the core's room: its
registers padded to `0^{c+1}` against the reference `sent c` and its cell written (`prepP`), then its run zero-padded to
the bank's register length and focused (`dock_stepM`). **`dock_stage`**: the outputs written, the input kept, the
block within `c + 1`, every other tape kept.

Paper quantity: none (the front's machine assembly, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length read_sent)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other install_existing)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj rTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c sTape_val rTape_val cTape_val)

section Dock
variable {u ns nr : ℕ}

/-- **A machine's run between two encodings, docked onto the bank.** -/
theorem dock_stepM {s : ℕ} (M : Machine (ns + 2 + nr) s) (slots : Fin (ns + 2 + nr) → Fin u)
    (hi : Function.Injective slots) (capW c : ℕ) (σ τ : WState ns nr) (n : ℕ)
    (hx : Step M n (wenc capW σ).H (wenc capW σ).A (wenc capW τ).H (wenc capW τ).A)
    (hσs : ∀ i, σ.sh i = 0) (hσv : ∀ q, σ.val q = 0) (hτs : ∀ i, τ.sh i = 0) (hτv : ∀ q, τ.val q = 0)
    (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW σ).A j)) :
    Step (RecoveryFocus.machine slots M) n (fun _ => 0) A (fun _ => 0)
      (install slots A (fun j => ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW τ).A j))) := by
  have hs := hx.pad (Bridge.pc ns nr c)
  rw [Bridge.wenc_H0 ns nr capW σ hσs hσv, Bridge.wenc_H0 ns nr capW τ hτs hτv] at hs
  have hf := hs.focus slots hi (fun _ => 0) A
  rw [dockH_zero slots hi, install_existing slots A _ hA] at hf
  exact hf

variable {m : ℕ} (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1)) (i0 : Fin u) (out : Fin m → Fin u)
  (room : Fin (ns + 2 + nr) → Fin u)

/-- A tape off the input, the outputs and the used room is no slot. -/
theorem wslots_ne (y : Fin u) (h0 : y ≠ i0) (ho : ∀ k, y ≠ out k)
    (hr : ∀ j, j ≠ sTape sIn → (∀ k, sTape (sOut k) ≠ j) → y ≠ room j) (hso : Function.Injective sOut)
    (hne : ∀ k, sOut k ≠ sIn) : ∀ j, wslots sIn sOut i0 out room j ≠ y := by
  intro j
  rcases slot_cases sIn sOut j with e | ⟨k, e⟩ | ⟨a, b⟩
  · subst e; rw [wslots_in]; exact fun e => h0 e.symm
  · subst e; rw [wslots_out _ _ _ _ _ hso hne]; exact fun e => ho k e.symm
  · rw [wslots_room _ _ _ _ _ _ a b]; exact fun e => hr j a b e.symm

end Dock

/-! ## One writer's stage -/

/-- The writer's register tapes in its block. -/
def regsOf {u ns nr : ℕ} (room : Fin (ns + 2 + nr) → Fin u) : List (Fin u) :=
  (List.finRange nr).map (fun q => room (rTape q))

theorem regsOf_length {u ns nr : ℕ} (room : Fin (ns + 2 + nr) → Fin u) : (regsOf room).length = nr := by
  simp [regsOf]

theorem mem_regsOf {u ns nr : ℕ} (room : Fin (ns + 2 + nr) → Fin u) (y : Fin u) :
    y ∈ regsOf room ↔ ∃ q : Fin nr, room (rTape q) = y := by
  simp [regsOf]

end NearCubicWires.WireExponent3_5.FinalPass.Core
