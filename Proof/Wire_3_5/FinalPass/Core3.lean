import Proof.Wire_3_5.FinalPass.Core2
import Proof.Wire_3_5.FinalPass.CoreIface

/-! # S5Core, part 3: a word program docked onto the bank (P3:3170-3181)

The core half runs word programs (its count, each word writer) on the bank by focus: the program's input stream on
the bank's input tape, its output streams on the output tapes, everything else on fresh tapes of the core's room.
The program's register tapes are pre-padded to the bank's register length `c + 1` (`0^{c+1}`, the padded
`regTape capW 0`), its cell tape set to `[false]`:

* **`wslots`** (the slot map) with `wslots_in`, `wslots_out`, `wslots_room`, **`wslots_inj`**;
* `dockH_zero`, `pc_s`, `pc_c`, `pc_r`, **`entry_eq`** (the bank's tapes are the padded encoding of the entry
  state), **`dock_step`** (the program's run as a `Step` of the focused machine, the bank's other tapes kept);
* `prepP`, **`prepP_exec`** (the register tapes padded against `sent c`, the cell tape written).

Paper quantity: none (the front's machine assembly, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other install_existing)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj rTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c sTape_val rTape_val cTape_val)

section Slots
variable {u ns nr m : ℕ}

/-- **The slot map**: the input stream on `i0`, output `k` on `out k`, every other tape `j` on `room j`. -/
noncomputable def wslots (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1)) (i0 : Fin u) (out : Fin m → Fin u)
    (room : Fin (ns + 2 + nr) → Fin u) (j : Fin (ns + 2 + nr)) : Fin u := by
  classical
  exact if j = sTape sIn then i0 else if h : ∃ k, sTape (sOut k) = j then out (Classical.choose h) else room j

variable (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1)) (i0 : Fin u) (out : Fin m → Fin u)
  (room : Fin (ns + 2 + nr) → Fin u)

theorem wslots_in : wslots sIn sOut i0 out room (sTape sIn) = i0 := by
  unfold wslots; simp

theorem wslots_out (hso : Function.Injective sOut) (hne : ∀ k, sOut k ≠ sIn) (k : Fin m) :
    wslots sIn sOut i0 out room (sTape (sOut k)) = out k := by
  classical
  unfold wslots
  have h1 : ¬ sTape (nr := nr) (sOut k) = sTape sIn := fun e => hne k (sTape_inj e)
  have h2 : ∃ k', sTape (nr := nr) (sOut k') = sTape (sOut k) := ⟨k, rfl⟩
  simp only [h1, if_false, dif_pos h2]
  congr 1
  exact hso (sTape_inj (Classical.choose_spec h2))

theorem wslots_room (j : Fin (ns + 2 + nr)) (h1 : j ≠ sTape sIn) (h2 : ∀ k, sTape (sOut k) ≠ j) :
    wslots sIn sOut i0 out room j = room j := by
  classical
  unfold wslots
  have h3 : ¬ ∃ k, sTape (nr := nr) (sOut k) = j := fun ⟨k, hk⟩ => h2 k hk
  simp only [h1, if_false, dif_neg h3]

theorem slot_cases (j : Fin (ns + 2 + nr)) :
    j = sTape sIn ∨ (∃ k, sTape (sOut k) = j) ∨ (j ≠ sTape sIn ∧ ∀ k, sTape (sOut k) ≠ j) := by
  by_cases h1 : j = sTape sIn
  · exact Or.inl h1
  · by_cases h2 : ∃ k, sTape (nr := nr) (sOut k) = j
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, fun k hk => h2 ⟨k, hk⟩⟩)

/-- **The slot map is injective.** -/
theorem wslots_inj (hso : Function.Injective sOut) (hne : ∀ k, sOut k ≠ sIn) (hout : Function.Injective out)
    (hroom : Function.Injective room) (h0o : ∀ k, out k ≠ i0) (h0r : ∀ j, room j ≠ i0) (hor : ∀ k j, out k ≠ room j) :
    Function.Injective (wslots sIn sOut i0 out room) := by
  intro j1 j2 h
  rcases slot_cases sIn sOut j1 with e1 | ⟨k1, e1⟩ | ⟨a1, b1⟩ <;>
    rcases slot_cases sIn sOut j2 with e2 | ⟨k2, e2⟩ | ⟨a2, b2⟩
  · rw [e1, e2]
  · subst e1 e2; rw [wslots_in, wslots_out _ _ _ _ _ hso hne] at h; exact absurd h.symm (h0o k2)
  · subst e1; rw [wslots_in, wslots_room _ _ _ _ _ _ a2 b2] at h; exact absurd h.symm (h0r j2)
  · subst e1 e2; rw [wslots_in, wslots_out _ _ _ _ _ hso hne] at h; exact absurd h (h0o k1)
  · subst e1 e2; rw [wslots_out _ _ _ _ _ hso hne, wslots_out _ _ _ _ _ hso hne] at h; rw [hout h]
  · subst e1; rw [wslots_out _ _ _ _ _ hso hne, wslots_room _ _ _ _ _ _ a2 b2] at h; exact absurd h (hor k1 j2)
  · subst e2; rw [wslots_in, wslots_room _ _ _ _ _ _ a1 b1] at h; exact absurd h (h0r j1)
  · subst e2; rw [wslots_out _ _ _ _ _ hso hne, wslots_room _ _ _ _ _ _ a1 b1] at h; exact absurd h.symm (hor k2 j1)
  · rw [wslots_room _ _ _ _ _ _ a1 b1, wslots_room _ _ _ _ _ _ a2 b2] at h; exact hroom h

end Slots

/-! ## The docked run -/

theorem dockH_zero {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) :
    dockH slots (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    exact dockH_slot _ hi _ _ j
  · exact dockH_other _ _ _ i (fun j e => h ⟨j, e⟩)

section Dock
variable {ns nr : ℕ}

theorem pc_s (c : ℕ) (i : Fin (ns + 1)) : Bridge.pc ns nr c (sTape (nr := nr) i) = 0 := by
  unfold Bridge.pc; rw [if_neg (by rw [sTape_val]; have := i.isLt; split_ifs <;> omega)]

theorem pc_c (c : ℕ) : Bridge.pc ns nr c (cTape (ns := ns) (nr := nr)) = 0 := by
  unfold Bridge.pc; rw [if_neg (by rw [cTape_val]; omega)]

theorem pc_r (c : ℕ) (q : Fin nr) : Bridge.pc ns nr c (rTape (ns := ns) q) = c + 1 := by
  unfold Bridge.pc; rw [if_pos (by rw [rTape_val]; omega)]

/-- **The bank's tapes are the padded encoding of the entry state.** -/
theorem entry_eq {u : ℕ} (slots : Fin (ns + 2 + nr) → Fin u) (capW c : ℕ) (hc : capW ≤ c) (σ : WState ns nr)
    (hv : ∀ q, σ.val q = 0) (A : Fin u → List Bool) (hs : ∀ i, A (slots (sTape i)) = σ.st i)
    (hcl : A (slots cTape) = [σ.cell]) (hr : ∀ q, A (slots (rTape q)) = List.replicate (c + 1) false) :
    ∀ j, A (slots j) = ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW σ).A j) := by
  intro j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [pc_s, ZeroPadding.pad_zero, wenc_A_s, hs]
  · rw [pc_c, ZeroPadding.pad_zero, wenc_A_c, hcl]
  · rw [pc_r, wenc_A_r, hv, regTape_zero, Bridge.pad_replicate capW c hc, hr]

/-- **A word program docked onto the bank.** -/
theorem dock_step {u : ℕ} (P : WM ns nr) (slots : Fin (ns + 2 + nr) → Fin u) (hi : Function.Injective slots)
    (capW c : ℕ) (σ τ : WState ns nr) (n : ℕ) (hx : WExec capW P σ τ n)
    (hσs : ∀ i, σ.sh i = 0) (hσv : ∀ q, σ.val q = 0) (hτs : ∀ i, τ.sh i = 0) (hτv : ∀ q, τ.val q = 0)
    (A : Fin u → List Bool) (hA : ∀ j, A (slots j) = ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW σ).A j)) :
    Step (RecoveryFocus.machine slots P.toProg.compile) n (fun _ => 0) A (fun _ => 0)
      (install slots A (fun j => ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW τ).A j))) := by
  have hs := (Exec.step (WExec.exec capW hx)).pad (Bridge.pc ns nr c)
  rw [Bridge.wenc_H0 ns nr capW σ hσs hσv, Bridge.wenc_H0 ns nr capW τ hτs hτv] at hs
  have hf := hs.focus slots hi (fun _ => 0) A
  rw [dockH_zero slots hi, install_existing slots A _ hA] at hf
  exact hf

/-- The exit bank at a stream's slot. -/
theorem exit_s {u : ℕ} (slots : Fin (ns + 2 + nr) → Fin u) (hi : Function.Injective slots) (capW c : ℕ)
    (τ : WState ns nr) (A : Fin u → List Bool) (i : Fin (ns + 1)) :
    install slots A (fun j => ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW τ).A j)) (slots (sTape i)) = τ.st i := by
  rw [install_slot _ hi, pc_s, ZeroPadding.pad_zero, wenc_A_s]

/-- The exit bank at the cell's slot. -/
theorem exit_c {u : ℕ} (slots : Fin (ns + 2 + nr) → Fin u) (hi : Function.Injective slots) (capW c : ℕ)
    (τ : WState ns nr) (A : Fin u → List Bool) :
    install slots A (fun j => ZeroPadding.pad (Bridge.pc ns nr c j) ((wenc capW τ).A j)) (slots cTape) = [τ.cell] := by
  rw [install_slot _ hi, pc_c, ZeroPadding.pad_zero, wenc_A_c]

end Dock

/-! ## The program's preparation -/

section Prep
variable {t : ℕ}

/-- **Prepare a program's tapes**: its registers padded to `0^{c+1}` against `T = sent c`, its cell written. -/
def prepP (T cl : Fin t) (regs : List (Fin t)) : Prog t := .seq (padList T regs) (.act (writeAt cl false) (fun _ => .stay))

theorem prepP_exec (T cl : Fin t) (c : ℕ) (regs : List (Fin t)) (b : Bank t) (hnd : regs.Nodup) (hT : T ∉ regs)
    (hcl : cl ∉ regs) (hA : b.A T = sent c) (hH : ∀ i, b.H i = 0) (hr : ∀ j ∈ regs, (b.A j).length ≤ c + 1)
    (hc : b.A cl = []) :
    Exec (prepP T cl regs) b ⟨fun _ => 0, fun i => if i = cl then [false] else if i ∈ regs then
      List.replicate (c + 1) false else b.A i⟩ (regs.length * (6 * c + 17) + 1 + 1) := by
  have e1 := padList_exec T c regs b hnd hT hA (hH T) (fun j hj => ⟨hH j, hr j hj⟩)
  have e2 := Exec.act (⟨b.H, fun i => if i ∈ regs then List.replicate (c + 1) false else b.A i⟩ : Bank t)
    (writeAt cl false) (fun _ => .stay)
  have hb : (⟨b.H, fun i => if i ∈ regs then List.replicate (c + 1) false else b.A i⟩ : Bank t).act (writeAt cl false)
      (fun _ => .stay) = ⟨fun _ => 0, fun i => if i = cl then [false] else if i ∈ regs then
        List.replicate (c + 1) false else b.A i⟩ := by
    apply Bank.ext'
    · intro i; simp [Bank.act, HeadMove.apply, hH]
    · intro i
      by_cases hi : i = cl
      · subst hi; simp [Bank.act, writeAt, hcl, hc, writeTapeBit, hH]
      · simp [Bank.act, writeAt, hi]
  rw [hb] at e2
  exact Exec.mono (Exec.seq e1 e2) le_rfl

end Prep

end NearCubicWires.WireExponent3_5.FinalPass.Core
