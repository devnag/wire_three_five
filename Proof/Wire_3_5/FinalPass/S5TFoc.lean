import Proof.Wire_3_5.FinalPass.S5TScrBase
import Proof.Wire_3_5.FinalPass.SeamsBank2Base

/-! # S5-THR, part 32: the THR half focused onto the front's bank (P3:3170-3181)

The THR half runs on its own tapes (the scrub's layout); S4's bank (`S5Lay`, `HalfRoom2`) hosts it: its input tape on
the bank's tape `0`, its THR slots `8 … 15` on the bank's word tapes `wd 8 … wd 15`, every other tape on the THR
scratch room `thrE` (`mThr` tapes). `RecoveryFocus.machine` runs it there (`Step.dock`).

* `mThr`, `idxT`, `slotMap` (+ inj), **`focus_run`**: the THR slots written, the THR scratch blank within the
  half's bound, every other tape of the bank kept.

Paper quantity of the main type: the THR half's exit on S4's bank (`S5Thr2.run`'s three facts). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Bank

section Foc
variable (D x6 xt : ℕ)

/-- The THR half's room: every tape of its scrub layout but the input and the eight THR slots. -/
def mThr : ℕ := nsL D x6 xt + nrL - 5

/-- The room index of a scratch tape (the cell `1 ↦ 0`, a tape `j ≥ 10 ↦ j − 9`). -/
def idxT (j : Fin (nsL D x6 xt + 2 + nrL + 1 + 1)) : Fin (mThr D x6 xt) :=
  ⟨if j.val = 1 then 0 else j.val - 9, by
    have := nsL_ge D x6 xt; have := j.isLt; unfold mThr; split_ifs <;> omega⟩

variable {nw : ℕ} (L : S5Lay nw) {mC : ℕ} (hR : HalfRoom2 L (mThr D x6 xt) mC)

/-- **The THR half's tapes on S4's bank.** -/
def slotMap (j : Fin (nsL D x6 xt + 2 + nrL + 1 + 1)) : Fin L.t :=
  if j.val = 0 then ⟨0, L.ht⟩ else if h : 2 ≤ j.val ∧ j.val ≤ 9 then L.wd ⟨8 + (j.val - 2), by omega⟩
  else hR.thrE (idxT D x6 xt j)

theorem slotMap_inj : Function.Injective (slotMap D x6 xt L hR) := by
  have hwd0 := L.in0
  have hoff := L.thrOff
  have hsc := hR.thrE_sc
  intro a b h
  unfold slotMap at h
  by_cases a0 : a.val = 0
  · by_cases b0 : b.val = 0
    · exact Fin.ext (by omega)
    · rw [if_pos a0, if_neg b0] at h
      split_ifs at h with hb
      · exact absurd (congrArg Fin.val h).symm (hwd0 _)
      · exact absurd (congrArg Fin.val h).symm (hoff _ (hsc _)).1
  · rw [if_neg a0] at h
    by_cases b0 : b.val = 0
    · rw [if_pos b0] at h
      split_ifs at h with ha
      · exact absurd (congrArg Fin.val h) (hwd0 _)
      · exact absurd (congrArg Fin.val h) (hoff _ (hsc _)).1
    · rw [if_neg b0] at h
      by_cases ha : 2 ≤ a.val ∧ a.val ≤ 9
      · by_cases hb : 2 ≤ b.val ∧ b.val ≤ 9
        · rw [dif_pos ha, dif_pos hb] at h
          have := congrArg Fin.val (L.wdInj h); simp at this; exact Fin.ext (by omega)
        · rw [dif_pos ha, dif_neg hb] at h
          exact absurd h.symm ((hoff _ (hsc _)).2.1 _)
      · by_cases hb : 2 ≤ b.val ∧ b.val ≤ 9
        · rw [dif_neg ha, dif_pos hb] at h
          exact absurd h ((hoff _ (hsc _)).2.1 _)
        · rw [dif_neg ha, dif_neg hb] at h
          have e := congrArg Fin.val (hR.thrE.injective h)
          simp only [idxT] at e
          apply Fin.ext
          split_ifs at e <;> omega

theorem slotMap_in (j : Fin (nsL D x6 xt + 2 + nrL + 1 + 1)) (hj : j.val = 0) :
    slotMap D x6 xt L hR j = ⟨0, L.ht⟩ := by unfold slotMap; rw [if_pos hj]

theorem slotMap_wd (j : Fin (nsL D x6 xt + 2 + nrL + 1 + 1)) (h0 : j.val ≠ 0) (h : 2 ≤ j.val ∧ j.val ≤ 9) :
    slotMap D x6 xt L hR j = L.wd ⟨8 + (j.val - 2), by omega⟩ := by unfold slotMap; rw [if_neg h0, dif_pos h]

theorem slotMap_scr (j : Fin (nsL D x6 xt + 2 + nrL + 1 + 1)) (h0 : j.val ≠ 0) (h : ¬ (2 ≤ j.val ∧ j.val ≤ 9)) :
    slotMap D x6 xt L hR j = hR.thrE (idxT D x6 xt j) := by unfold slotMap; rw [if_neg h0, dif_neg h]

theorem sTape_sIn_val : (Scrub.inner (sTape (nr := nrL) (sIn D x6 xt))).val = 0 := rfl

theorem sTape_sSlot_val (m : Fin 8) : (Scrub.inner (sTape (nr := nrL) (sSlot D x6 xt m))).val = 2 + m.val := by
  rw [Scrub.inner_val, PrimAsm.DockW.sTape_val]; simp [sSlot]; omega

theorem slotMap_slot (m : Fin 8) :
    slotMap D x6 xt L hR (Scrub.inner (sTape (sSlot D x6 xt m))) = L.wd ⟨8 + m.val, by omega⟩ := by
  have hv := sTape_sSlot_val D x6 xt m
  rw [slotMap_wd D x6 xt L hR _ (by omega) (by omega)]
  congr 1; apply Fin.ext; simp only; omega

/-- **The THR half focused onto S4's bank.** -/
theorem focus_run {s n : ℕ} (M : Machine (nsL D x6 xt + 2 + nrL + 1 + 1) s) (u : List Bool)
    (Af : Fin (nsL D x6 xt + 2 + nrL + 1 + 1) → List Bool) (w : Fin 8 → List Bool) (Lb : ℕ)
    (hstep : Step M n (fun _ => 0) (A02 u) (fun _ => 0) Af)
    (hin : Af (Scrub.inner (sTape (sIn D x6 xt))) = frame u)
    (hslot : ∀ m : Fin 8, Af (Scrub.inner (sTape (sSlot D x6 xt m))) = w m)
    (hbl : ∀ j, j ≠ Scrub.inner (sTape (sIn D x6 xt)) → (∀ m, j ≠ Scrub.inner (sTape (sSlot D x6 xt m))) →
      ∃ ℓ ≤ Lb, Af j = List.replicate ℓ false)
    (Ab : Fin L.t → List Bool) (hAb0 : Ab ⟨0, L.ht⟩ = frame u) (hAbS : ∀ k, thrSlot k → Ab (L.wd k) = [])
    (hAbT : ∀ j, L.thrSc j = true → Ab j = []) :
    ∃ Ab', Step (RecoveryFocus.machine (slotMap D x6 xt L hR) M) n (fun _ => 0) Ab (fun _ => 0) Ab' ∧
      (∀ k (hk : thrSlot k), Ab' (L.wd k) = w ⟨k.val - 8, by have := hk.2; omega⟩) ∧
      (∀ j, L.thrSc j = true → ∃ ℓ ≤ Lb, Ab' j = List.replicate ℓ false) ∧
      (∀ j, L.thrSc j = false → (∀ k, thrSlot k → j ≠ L.wd k) → Ab' j = Ab j) := by
  have hinj := slotMap_inj D x6 xt L hR
  have hge := nsL_ge D x6 xt
  have hs := hstep.dock (slotMap D x6 xt L hR) hinj (fun _ => 0) Ab (fun _ => rfl) (fun j => by
    unfold slotMap A02
    by_cases h0 : j.val = 0
    · rw [if_pos h0, if_pos h0, hAb0]
    · rw [if_neg h0, if_neg h0]
      split_ifs with h
      · exact hAbS _ ⟨by simp, by simp; omega⟩
      · exact hAbT _ (hR.thrE_sc _))
  have hdz : dockH (slotMap D x6 xt L hR) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
    funext i
    by_cases hi : ∃ j, slotMap D x6 xt L hR j = i
    · obtain ⟨j, rfl⟩ := hi; rw [dockH_slot _ hinj]
    · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩)]
  rw [hdz] at hs
  refine ⟨_, hs, ?_, ?_, ?_⟩
  · intro k hk
    have hk1 := hk.1; have hk2 := hk.2
    have e : L.wd k = slotMap D x6 xt L hR (Scrub.inner (sTape (sSlot D x6 xt ⟨k.val - 8, by omega⟩))) := by
      rw [slotMap_slot]; congr 1; apply Fin.ext; simp only; omega
    rw [e, install_slot _ hinj, hslot]
  · intro j hj
    by_cases hr : ∃ i, slotMap D x6 xt L hR i = j
    · obtain ⟨i, rfl⟩ := hr
      rw [install_slot _ hinj]
      have hoff := L.thrOff _ hj
      refine hbl i (fun e => ?_) (fun m e => ?_)
      · rw [e, slotMap_in D x6 xt L hR _ (sTape_sIn_val D x6 xt)] at hoff; exact hoff.1 rfl
      · rw [e, slotMap_slot] at hoff
        exact hoff.2.1 _ rfl
    · rw [install_other _ _ _ _ (fun i h => hr ⟨i, h⟩), hAbT j hj]; exact ⟨0, by omega, rfl⟩
  · intro j hj hk
    by_cases hr : ∃ i, slotMap D x6 xt L hR i = j
    · obtain ⟨i, rfl⟩ := hr
      rw [install_slot _ hinj]
      by_cases h0 : i.val = 0
      · rw [slotMap_in D x6 xt L hR i h0,
          show i = Scrub.inner (sTape (sIn D x6 xt)) from Fin.ext (by rw [sTape_sIn_val]; exact h0), hin, hAb0]
      · by_cases h : 2 ≤ i.val ∧ i.val ≤ 9
        · rw [slotMap_wd D x6 xt L hR i h0 h] at hk
          exact absurd rfl (hk ⟨8 + (i.val - 2), by omega⟩ ⟨by simp, by simp; omega⟩)
        · rw [slotMap_scr D x6 xt L hR i h0 h, hR.thrE_sc] at hj; exact absurd hj (by decide)
    · rw [install_other _ _ _ _ (fun i h => hr ⟨i, h⟩)]

end Foc

end NearCubicWires.WireExponent3_5.FinalPass.S5T
