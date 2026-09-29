import Proof.Wire_3_5.FinalPass.Core4

/-! # S5Core, part 5: the reference erased, the branch, one writer's stage on the bank (P3:3170-3181)

* `eraseS` / **`eraseS_exec`** (the reference `sent c` → `0^{c+1}`, its head back at `0`: to the end over the ones,
  then back writing zeros until the sentinel);
* **`iteM_T`**, **`iteM_F`** (the branch machine takes the branch its test bit names);
* **`dock_stepM`** (a machine's `Step` between the encodings of two word states, registers zero-padded to the bank's
  `c + 1`, focused onto the bank), **`dock_stage`** (one writer's stage: its registers padded against the reference
  `sent c`, its cell written, its run focused; its outputs written, the input kept, its room within `c + 1`, every other
  tape kept).

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

section Erase
variable {t : ℕ}

/-- **Erase the reference**: one right, over the ones, one left, then zeros leftwards to the sentinel. -/
def eraseS (j : Fin t) : Prog t :=
  .seq (.act (fun _ => none) (moveAt j .right)) (.seq (.loop j (.act (fun _ => none) (moveAt j .right)))
    (.seq (.act (fun _ => none) (moveAt j .left)) (.loop j (.act (writeAt j false) (moveAt j .left)))))

theorem fwdS_exec (j : Fin t) (c : ℕ) : ∀ (m : ℕ) (b : Bank t), b.A j = sent c → 1 ≤ b.H j → b.H j + m = c + 1 →
    Exec (.loop j (.act (fun _ => none) (moveAt j .right))) b ⟨Function.update b.H j (c + 1), b.A⟩ (3 * m + 1)
  | 0, b, hA, _, hH => by
    have hb : b.bit j = false := by unfold Bank.bit; rw [hA, read_sent]; simp; omega
    have e : (⟨Function.update b.H j (c + 1), b.A⟩ : Bank t) = b := by
      rw [show c + 1 = b.H j by omega, Function.update_eq_self]
    rw [e]; exact Exec.loopF hb
  | m + 1, b, hA, h1, hH => by
    have hb : b.bit j = true := by unfold Bank.bit; rw [hA, read_sent]; simp; omega
    have e1 := Exec.act b (fun _ => none) (moveAt j .right)
    have ih := fwdS_exec j c m (b.act (fun _ => none) (moveAt j .right)) (by simp [Bank.act, hA])
      (by simp [Bank.act, moveAt, HeadMove.apply]) (by simp [Bank.act, moveAt, HeadMove.apply]; omega)
    have e : (⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j (c + 1),
        (b.act (fun _ => none) (moveAt j .right)).A⟩ : Bank t) = ⟨Function.update b.H j (c + 1), b.A⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; simp [Bank.act]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

theorem wr_ones (R : List Bool) : ∀ h : ℕ,
    writeTapeBit (List.replicate (h + 1) true ++ R) h false = List.replicate h true ++ false :: R
  | 0 => rfl
  | h + 1 => by
    show true :: writeTapeBit (List.replicate (h + 1) true ++ R) h false = _
    rw [wr_ones R h]; rfl

theorem bwdS_exec (j : Fin t) (c : ℕ) : ∀ (h : ℕ) (b : Bank t),
    b.A j = false :: (List.replicate h true ++ List.replicate (c - h) false) → b.H j = h → h ≤ c →
    Exec (.loop j (.act (writeAt j false) (moveAt j .left))) b
      ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (c + 1) false)⟩ (3 * h + 1)
  | 0, b, hA, hH, _ => by
    have hb : b.bit j = false := by unfold Bank.bit; rw [hA, hH]; rfl
    have e : (⟨Function.update b.H j 0, Function.update b.A j (List.replicate (c + 1) false)⟩ : Bank t) = b := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp [hH]
        · simp [Function.update_apply, hi]
      · intro i; by_cases hi : i = j
        · subst hi; simp [hA, List.replicate_succ]
        · simp [Function.update_apply, hi]
    rw [e]; exact Exec.loopF hb
  | h + 1, b, hA, hH, hh => by
    have hb : b.bit j = true := by
      unfold Bank.bit; rw [hA, hH]
      show readTapeBit (List.replicate (h + 1) true ++ List.replicate (c - (h + 1)) false) h = true
      unfold readTapeBit
      rw [List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    have e1 := Exec.act b (writeAt j false) (moveAt j .left)
    have hw : (b.act (writeAt j false) (moveAt j .left)).A j =
        false :: (List.replicate h true ++ List.replicate (c - h) false) := by
      simp only [Bank.act, writeAt, if_pos rfl, hA, hH]
      show false :: writeTapeBit (List.replicate (h + 1) true ++ List.replicate (c - (h + 1)) false) h false = _
      rw [wr_ones, show c - h = (c - (h + 1)) + 1 by omega, List.replicate_succ]
    have ih := bwdS_exec j c h (b.act (writeAt j false) (moveAt j .left)) hw
      (by simp [Bank.act, moveAt, HeadMove.apply, hH]) (by omega)
    have e : (⟨Function.update (b.act (writeAt j false) (moveAt j .left)).H j 0,
        Function.update (b.act (writeAt j false) (moveAt j .left)).A j (List.replicate (c + 1) false)⟩ : Bank t) =
        ⟨Function.update b.H j 0, Function.update b.A j (List.replicate (c + 1) false)⟩ := by
      apply Bank.ext'
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
      · intro i; by_cases hi : i = j
        · subst hi; simp
        · simp [Function.update_apply, hi, Bank.act, writeAt]
    rw [e] at ih
    exact Exec.mono (Exec.loopT hb e1 ih) (by omega)

/-- **The reference erased**: `sent c` → `0^{c+1}`, its head back at `0`, every other tape and head kept. -/
theorem eraseS_exec (j : Fin t) (c : ℕ) (b : Bank t) (hA : b.A j = sent c) (hH : b.H j = 0) :
    Exec (eraseS j) b ⟨b.H, Function.update b.A j (List.replicate (c + 1) false)⟩ (6 * c + 10) := by
  have e1 := Exec.act b (fun _ => none) (moveAt j .right)
  have h1 : (b.act (fun _ => none) (moveAt j .right)).H j = 1 := by simp [Bank.act, moveAt, HeadMove.apply, hH]
  have e2 := fwdS_exec j c c (b.act (fun _ => none) (moveAt j .right)) (by simp [Bank.act, hA]) (by omega) (by omega)
  have e3 := Exec.act (⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j (c + 1),
    (b.act (fun _ => none) (moveAt j .right)).A⟩ : Bank t) (fun _ => none) (moveAt j .left)
  have e4 := bwdS_exec j c c (Bank.act ⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j (c + 1),
    (b.act (fun _ => none) (moveAt j .right)).A⟩ (fun _ => none) (moveAt j .left))
    (by simp [Bank.act, hA, sent]) (by simp [Bank.act, moveAt, HeadMove.apply]) le_rfl
  have hfin : (⟨Function.update (Bank.act ⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j (c + 1),
      (b.act (fun _ => none) (moveAt j .right)).A⟩ (fun _ => none) (moveAt j .left)).H j 0,
      Function.update (Bank.act ⟨Function.update (b.act (fun _ => none) (moveAt j .right)).H j (c + 1),
      (b.act (fun _ => none) (moveAt j .right)).A⟩ (fun _ => none) (moveAt j .left)).A j
        (List.replicate (c + 1) false)⟩ : Bank t) = ⟨b.H, Function.update b.A j (List.replicate (c + 1) false)⟩ := by
    apply Bank.ext'
    · intro i; by_cases hi : i = j
      · subst hi; simp [hH]
      · simp [Function.update_apply, hi, Bank.act, moveAt, HeadMove.apply]
    · intro i; by_cases hi : i = j
      · subst hi; simp
      · simp [Function.update_apply, hi, Bank.act]
  rw [hfin] at e4
  exact Exec.mono (Exec.seq e1 (Exec.seq e2 (Exec.seq e3 e4))) (by omega)

end Erase

/-! ## The branch -/

section Ite
variable {t : ℕ}

theorem iteM_T (i : Fin t) {a b' : ℕ} (p : Machine t a) (q : Machine t b') (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = true) (h : Step p n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteL b') p (by simp [hb]) (ite_halted_L i p q) (ite_step_L i p q) h

theorem iteM_F (i : Fin t) {a b' : ℕ} (p : Machine t a) (q : Machine t b') (bk c : Bank t) (n : ℕ)
    (hb : bk.bit i = false) (h : Step q n bk.H bk.A c.H c.A) : Step (iteMachine i p q) (n + 1) bk.H bk.A c.H c.A :=
  ite_branch_step i p q bk c n (iteR a) q (by simp [hb]) (ite_halted_R i p q) (ite_step_R i p q) h

end Ite

end NearCubicWires.WireExponent3_5.FinalPass.Core
