import Proof.Wire_3_5.Primitive.SeedFix.C4CapC

/-! # c4 THR block, the THR setup's numbers on the layout: the counts' copy-in and the numbers machine

`mid_run2` after its data stage (steps 7-8), for any register program `P` (the THR numbers program `bigWT` in
the THR stage). From the data word on `gDO`, the request on `gP0` and `1^W` on `gUW` (the bank blank from the copy's
region up), the numbers machine's thirty-nine words land on `gW` (**`cb_run`**).

Paper quantity of the main type: the loop's entry words (the numbers machine's streams `symO`) on their tapes
(P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set

variable (L : Lay)

/-- **The copy-in and the numbers machine** of program `P` on the layout. -/
noncomputable def cbM (P : WM (LNS 0) LNR) :=
  Composition.machine (RecoveryFocus.machine (slx L.oCP (by unfold Lay.oCP; rw [Lay.N_eq]; omega) (ext0 L.gDO)) cpZ)
    (RecoveryFocus.machine (slx L.oBG (by have : BX = 676 := rfl; unfold Lay.oBG; rw [Lay.N_eq]; omega) L.extBG)
      (bigM P))

/-- Its step bound. -/
def cbCost (u : List Bool) (W c : ℕ) : ℕ := cpZCost u + 1 + bigCost W c

/-- **The copy-in and the numbers machine, run.** -/
theorem cb_run (P : WM (LNS 0) LNR) (W : ℕ) (w : List Bool) (cs : List ℕ) (τ : WState (LNS 0) LNR) (c : ℕ)
    (hx : WExec (2 * W + 2) P (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList cs)) τ c)
    (hτ0 : τ.st (sk 0 0) = frame w) (wd : Fin 39 → List Bool) (hτ : ∀ j, τ.st (sk 0 (symO j)) = wd j)
    (B6 : Fin L.N → List Bool) (f6P0 : B6 L.gP0 = frame w) (f6DO : B6 L.gDO = Data.dataWord cs)
    (f6W : B6 L.gUW = List.replicate W true) (bl6 : ∀ i : Fin L.N, L.oCP ≤ i.val → B6 i = []) :
    ∃ B8 : Fin L.N → List Bool, Step (cbM L P) (cbCost (Data.unaryList cs) W c) (fun _ => 0) B6 (fun _ => 0) B8 ∧
      B8 L.gP0 = frame w ∧ (∀ j, B8 (L.gW j) = wd j) ∧ (∀ i : Fin L.N, i.val < 3 → i ≠ L.gP0 → B8 i = B6 i) ∧
      (∀ i : Fin L.N, L.oM1 ≤ i.val → B8 i = []) := by
  have hU := L.U_pos
  have ho := L.out_lt
  have hUe := L.U_eq
  have eDS : Data.DS = 9883 := rfl
  have eDR : Data.DR = 16 := rfl
  have eBX : BX = 676 := rfl
  have eBT : BT = 674 := rfl
  -- 7: the copy-in
  obtain ⟨t7, h7, e72⟩ := cpS (Data.unaryList cs)
  obtain ⟨B7, s7, bl7, un7, pv7, ex7⟩ := stage0 h7 (by norm_num) L.oCP (by unfold Lay.oCP; rw [Lay.N_eq]; omega) L.gDO
    (by lv) B6 (by rw [f6DO]; unfold Data.dataWord; rw [Modulus.frame_eq_marks]) bl6
  have f7P0 : B7 L.gP0 = frame w := (un7 _ (by lv) (by lv)).trans f6P0
  have f7W : B7 L.gUW = List.replicate W true := (un7 _ (by lv) (by lv)).trans f6W
  have f7U : B7 L.gU = Data.unaryList cs := (pv7 ⟨2, by norm_num⟩ L.gU (by norm_num) (by lv)).trans e72
  -- 8: the numbers machine
  obtain ⟨m8, h8⟩ := big_step P w (Data.unaryList cs) W τ c hx
  obtain ⟨B8, s8, bl8, un8, pv8, ex8⟩ := stageE h8 L.oBG (by unfold Lay.oBG; rw [Lay.N_eq]; omega) L.extBG
    (fun i j g hi hj => by
      unfold Lay.extBG at hi hj
      split_ifs at hi hj <;> simp at hi hj <;> subst_vars <;>
        first
        | exact Fin.ext (by omega)
        | (exfalso; revert hj; lv))
    (fun i g hi => by
      unfold Lay.extBG at hi
      split_ifs at hi <;> simp at hi <;> subst hi <;> lv)
    B7
    (fun j g hj => by
      unfold Lay.extBG at hj
      split_ifs at hj with a0 a2 a3 <;> simp at hj <;> subst hj <;> rw [ac_lt _ _ j (by omega)]
      · rw [f7P0]; simp [rawB, Fin.ext_iff, C4Set.vb0, a0]
      · rw [f7U]; simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, a2]
      · rw [f7W]; simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, C4Set.vcnt, a3])
    (fun i hi => bl7 i (by unfold Lay.oBG at hi; unfold Lay.oCP; omega))
    (fun j hj => by
      unfold Lay.extBG at hj
      split_ifs at hj with a0 a2 a3 <;> simp at hj
      by_cases hlt : j.val < BX
      · rw [ac_lt _ _ j hlt]
        simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, C4Set.vcnt, a0, a2, a3]
      · rw [ac_ge _ _ j (by omega)])
  refine ⟨B8, s7.seq s8, ?_, ?_, ?_, ?_⟩
  · rw [ex8 ⟨0, by norm_num⟩ L.gP0 (by simp [Lay.extBG]), ac_lt _ _ _ (by norm_num), ac_lt _ _ _ (by norm_num)]
    have e : (⟨0, by norm_num⟩ : Fin BT) = sTape (nr := LNR) (sk 0 0) := rfl
    rw [e, wenc_A_s, hτ0]
  · intro j
    have hs1 := Lay.symO_ge j
    have hs2 := Lay.symO_le j
    have hne : symO j ≠ 0 := fun e => by rw [e] at hs1; simp at hs1
    have hx : L.extBG ⟨1 + (symO j).val, by omega⟩ = none := by
      unfold Lay.extBG
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [pv8 ⟨1 + (symO j).val, by omega⟩ (L.gW j) hx (by lv), ac_lt _ _ _ (by simp; omega),
      ac_lt _ _ _ (by simp; omega)]
    have e : (⟨1 + (symO j).val, by omega⟩ : Fin BT) = sTape (nr := LNR) (sk 0 (symO j)) :=
      Fin.ext (by simp [sTape, sk, hne] <;> omega)
    rw [e, wenc_A_s, hτ]
  · intro i hi hne
    have n2 : i ≠ L.gU := fun e => by rw [e] at hi; revert hi; lv
    have n3 : i ≠ L.gUW := fun e => by rw [e] at hi; revert hi; lv
    have n4 : i ≠ L.gDO := fun e => by rw [e] at hi; revert hi; lv
    rw [un8 i (by unfold Lay.oBG; omega) (L.extBG_ne i hne n2 n3), un7 i (by unfold Lay.oCP; omega) n4]
  · intro i hi
    exact bl8 i (by unfold Lay.oBG; unfold Lay.oM1 at hi; omega)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
