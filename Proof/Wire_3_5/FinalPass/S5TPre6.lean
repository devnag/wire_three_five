import Proof.Wire_3_5.FinalPass.S5TPre5

/-! # S5-THR, part 21: the prelude as a machine on the scrub's layout (P3:3170-3181)

From the final pass's entry bank (the framed input on tape `0`, every other tape blank, every head at `0`) on the
scrub's layout `(ns + 2 + nr) + 1 + 1` (the register-program layout, the log, the driver):
1. the stage's cell `[false]` (`cellP2`);
2. the padded count program `preSub2` on its own register-free layout, docked (`Step.dock`): its streams on the
   stage's streams by `fs`, its count `C = 1^W` on the scrub's DRIVER (`preSlots2`);
3. `FrontFill.fillP` from the driver: every register tape `0^{2W+3}`, the scrub's LOG likewise.

**`pre_step2`**: the whole prelude as one `Step`, ending at `Scrub.bank (wenc (2W+2) σ02).A W (2W+3)` with every
head at `0`: the scrub's source bank (`Scrub.step`'s entry) with `R = W`, `L = 2W + 3`.

Paper quantity of the main type: the front's register capacity `2W + 2`, `W = (|fpIn| + 1 + c0)^{D+1}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj sTape_ne_c sTape_ne_r cTape_ne_r wslot
  wslot_s wslot_c wenc_A_c wenc_H_c)

variable {ns nr : ℕ}

theorem wenc0_H2 (D : ℕ) (σ : WState (D + 4) 0) (hs : ∀ i, σ.sh i = 0) : (wenc 0 σ).H = fun _ => 0 := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s, hs]
  · rw [wenc_H_c]
  · exact r.elim0

/-- The stage's cell `[false]` on the scrub's layout. -/
def cellP2 : Prog (ns + 2 + nr + 1 + 1) := .act (writeAt (Scrub.inner cTape) false) (fun _ => .stay)

/-- The stage's register tapes on the scrub's layout. -/
def regSel2 (j : Fin (ns + 2 + nr + 1 + 1)) : Bool := decide (ns + 2 ≤ j.val ∧ j.val < ns + 2 + nr)

theorem regSel2_s (i : Fin (ns + 1)) : regSel2 (Scrub.inner (sTape (nr := nr) i)) = false := by
  have := i.isLt
  simp only [regSel2, Scrub.inner_val, PrimAsm.DockW.sTape_val, decide_eq_false_iff_not, not_and, not_lt]
  split <;> omega

theorem regSel2_c : regSel2 (Scrub.inner (cTape (ns := ns) (nr := nr))) = false := by
  simp only [regSel2, Scrub.inner_val, PrimAsm.DockW.cTape_val, decide_eq_false_iff_not, not_and, not_lt]; omega

theorem regSel2_r (r : Fin nr) : regSel2 (Scrub.inner (rTape (ns := ns) r)) = true := by
  have := r.isLt
  simp only [regSel2, Scrub.inner_val, PrimAsm.DockW.rTape_val, decide_eq_true_eq]; omega

theorem regSel2_log : regSel2 (Scrub.logTape : Fin (ns + 2 + nr + 1 + 1)) = false := by
  simp only [regSel2, Scrub.log_val, decide_eq_false_iff_not, not_and, not_lt]; omega

theorem regSel2_drv : regSel2 (Scrub.driverTape : Fin (ns + 2 + nr + 1 + 1)) = false := by
  simp only [regSel2, Scrub.driver_val, decide_eq_false_iff_not, not_and, not_lt]; omega

theorem inner_inj {t : ℕ} : Function.Injective (Scrub.inner (t := t)) := fun a b h => by
  have := congrArg Fin.val h; rw [Scrub.inner_val, Scrub.inner_val] at this; exact Fin.ext this

/-- The count program's slots: its streams by `fs`, its count on the scrub's driver, its cell on the stage's cell. -/
def preSlots2 (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) (j : Fin (D + 4 + 2 + 0)) : Fin (ns + 2 + nr + 1 + 1) :=
  if j = sTape (nr := 0) (sC2 D) then Scrub.driverTape else Scrub.inner (wslot (nr := nr) fs Fin.elim0 j)

theorem preSlots2_C (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) :
    preSlots2 (nr := nr) D fs (sTape (sC2 D)) = Scrub.driverTape := by
  unfold preSlots2; rw [if_pos rfl]

theorem preSlots2_s (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) (k : Fin (D + 5)) (hk : k ≠ sC2 D) :
    preSlots2 (nr := nr) D fs (sTape k) = Scrub.inner (sTape (fs k)) := by
  unfold preSlots2; rw [if_neg (fun h => hk (sTape_inj h)), wslot_s]

theorem preSlots2_c (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) :
    preSlots2 (nr := nr) D fs cTape = Scrub.inner cTape := by
  unfold preSlots2; rw [if_neg (fun h => sTape_ne_c _ h.symm), wslot_c]

theorem preSlots2_inj (D : ℕ) (fs : Fin (D + 5) → Fin (ns + 1)) (hfs : Function.Injective fs) :
    Function.Injective (preSlots2 (nr := nr) D fs) := by
  have key : ∀ a : Fin (D + 4 + 2 + 0), preSlots2 (nr := nr) D fs a = Scrub.driverTape → a = sTape (sC2 D) := by
    intro a h
    rcases tape_cases a with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
    · by_cases hk : k = sC2 D
      · rw [hk]
      · rw [preSlots2_s D fs k hk] at h; exact absurd h (Scrub.inner_ne_driver _)
    · rw [preSlots2_c] at h; exact absurd h (Scrub.inner_ne_driver _)
    · exact r.elim0
  intro a b h
  by_cases ha : a = sTape (sC2 D)
  · rw [ha, preSlots2_C] at h; rw [ha, key b h.symm]
  · have hb : b ≠ sTape (sC2 D) := fun hb => ha (key a (by rw [h, hb, preSlots2_C]))
    unfold preSlots2 at h
    rw [if_neg ha, if_neg hb] at h
    exact preSlots_inj (D + 1) fs hfs (inner_inj h)

/-- The final pass's entry bank on the scrub's layout: the framed input on tape `0`. -/
def A02 (u : List Bool) : Fin (ns + 2 + nr + 1 + 1) → List Bool := fun j => if j.val = 0 then frame u else []

end NearCubicWires.WireExponent3_5.FinalPass.S5T
