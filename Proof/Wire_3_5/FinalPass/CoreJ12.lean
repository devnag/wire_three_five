import Proof.Wire_3_5.FinalPass.CoreJ11

/-! # S5Core over the writers with arbitrary residues, part J12: the THR half's exit and the count and mode stages on it (P3:3083-3086, 3170-3181)

* **`exit_factsJ`**: at the THR half's exit (`ThrExit2`) the input is on tape `0`, the core's room is blank, the
  non-THR word slots and the number tapes are blank;
* **`stage12J`**: the count then the mode from that exit: the reference `TcJ = sent c` (`c = L.Kc·N^{L.Dc}`), the mode
  tape `[thrFlag mode]`, the room invariant at `10`, every tape off the room kept.

Paper quantities: the front's exact register length (`FrontOut.blank`) and the request's mode (P3:3083-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)

section Run
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {mTh : ℕ}
  (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- **The THR half's exit, as the core reads it.** -/
theorem exit_factsJ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool)
    (hE : ThrExit2 l F kclk coef A a ha Sw0 L r Ab) :
    Ab (i0 L) = frame (fpIn l F kclk coef A a ha r) ∧ (∀ i, Ab (hR.coreE i) = []) ∧
      (∀ k, ¬ thrSlot k → Ab (L.wd k) = []) ∧ Ab L.tN = [] ∧ Ab L.tD = [] := by
  refine ⟨hE.input, fun i => ?_, hE.core, hE.num.1, hE.num.2⟩
  obtain ⟨h0, hw, hN, hD⟩ := core_off L hR i
  refine hE.rest _ h0 hw hN hD ?_
  cases h : L.thrSc (hR.coreE i)
  · rfl
  · have := L.disj _ h; rw [hR.coreE_sc i] at this; exact absurd this (by decide)

/-- **The count and the mode.** -/
theorem stage12J (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool)
    (hE : ThrExit2 l F kclk coef A a ha Sw0 L r Ab)
    (hc2 : 2 * ((fpIn l F kclk coef A a ha r).length + 1) ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) :
    ∃ A1 A2 : Fin L.t → List Bool,
      Step (cntM L hR (h5WJ W) L.Kc L.Dc) (1 + 1 + cntCost (fpIn l F kclk coef A a ha r).length L.Kc L.Dc)
        (fun _ => 0) Ab (fun _ => 0) A1 ∧
      Step (modeM L hR (h10WJ W) (cTtJ W L hR)) (1 + 1 + modeCost (natBitLength r.1.n)
          ((fpIn l F kclk coef A a ha r).length + 1)) (fun _ => 0) A1 (fun _ => 0) A2 ∧
      A2 (i0 L) = frame (fpIn l F kclk coef A a ha r) ∧
      A2 (TcJ W L hR) = sent (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) ∧
      A2 (MbJ W L hR) = [thrFlag r.1.mode] ∧
      RInv L hR (L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) A2 10 ∧
      (∀ y, (∀ i, hR.coreE i ≠ y) → A2 y = Ab y) := by
  classical
  set u := fpIn l F kclk coef A a ha r with hu
  set c := L.Kc * (u.length + 1) ^ L.Dc with hc
  obtain ⟨h0, hroom0, _, _, _⟩ := exit_factsJ W F kclk coef A a ha L hR r Ab hE
  obtain ⟨A1, s1, a1in, a1T, a1c, a1len, a1keep⟩ := cnt_stage L hR (h5WJ W) L.Kc L.Dc u Ab h0 (fun j => hroom0 _)
  obtain ⟨rest, hshape⟩ := fpIn_shape l F kclk coef A a ha r
  have hlen : 2 * natBitLength r.1.n + 2 ≤ u.length := fpIn_len l F kclk coef A a ha r
  have hcT0 : cTtJ W L hR ≠ i0 L := blk_ne0 L hR 0 _ (h5WJ W) _
  have hcTb : ∀ j, cTtJ W L hR ≠ blk L hR 5 (3 + 2 + 0) (h10WJ W) j := fun j =>
    blk_ne L hR 0 _ (h5WJ W) 5 _ (h10WJ W) (by omega) _ _
  have hA1b : ∀ j, A1 (blk L hR 5 (3 + 2 + 0) (h10WJ W) j) = [] := fun j => by
    rw [a1keep _ (fun j' => (blk_ne L hR 0 _ (h5WJ W) 5 _ (h10WJ W) (by omega) j' j).symm)]
    exact hroom0 _
  obtain ⟨A2, s2, a2M, a2len, a2keep⟩ := mode_stage L hR (h10WJ W) (cTtJ W L hR) hcT0 hcTb (natBitLength r.1.n)
    (u.length + 1) (WilliamsPublishedForm.fixedWidthNatBits (natBitLength r.1.n) r.1.n) (thrFlag r.1.mode) rest
    (fixed_len _ _) (by omega) A1 (by rw [a1in, ← hshape]) a1T hA1b
  have hTc2 : A2 (TcJ W L hR) = sent c := by
    rw [a2keep _ (fun j => by rw [Tc_eqJ]; exact blk_ne L hR 0 _ (h5WJ W) 5 _ (h10WJ W) (by omega) _ _), Tc_eqJ, a1c]
  refine ⟨A1, A2, s1, s2, ?_, hTc2, a2M, fun i => ?_, fun y hy => ?_⟩
  · rw [a2keep _ (fun j => (blk_ne0 L hR 5 _ (h10WJ W) j).symm), a1in]
  · by_cases h1 : i.val < 5
    · have e : hR.coreE i = blk L hR 0 (3 + 2 + 0) (h5WJ W) ⟨i.val, h1⟩ := by
        unfold blk; congr 1; exact Fin.ext (by simp)
      rw [e, a2keep _ (fun j => blk_ne L hR 0 _ (h5WJ W) 5 _ (h10WJ W) (by omega) _ _)]
      refine ⟨(a1len _).trans (max_le (by omega) le_rfl), fun h' => by omega⟩
    · by_cases h2 : i.val < 10
      · have e : hR.coreE i = blk L hR 5 (3 + 2 + 0) (h10WJ W) ⟨i.val - 5, by omega⟩ := by
          unfold blk; congr 1; exact Fin.ext (by simp; omega)
        rw [e]
        refine ⟨(a2len _).trans ?_, fun h' => by omega⟩
        omega
      · have hne5 : ∀ j, hR.coreE i ≠ blk L hR 5 (3 + 2 + 0) (h10WJ W) j := fun j e => by
          have := congrArg Fin.val (hR.coreE.injective e); simp only at this; have := j.isLt; omega
        have hne0 : ∀ j, hR.coreE i ≠ blk L hR 0 (3 + 2 + 0) (h5WJ W) j := fun j e => by
          have := congrArg Fin.val (hR.coreE.injective e); simp only at this; have := j.isLt; omega
        rw [a2keep _ hne5, a1keep _ hne0, hroom0]
        exact ⟨by simp, fun _ => rfl⟩
  · rw [a2keep _ (fun j e => hy _ e.symm), a1keep _ (fun j e => hy _ e.symm)]

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core
