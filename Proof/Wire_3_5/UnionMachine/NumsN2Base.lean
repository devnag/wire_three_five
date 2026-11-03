import Proof.Wire_3_5.UnionMachine.NumsN1
import Proof.Wire_3_5.UnionMachine.NumsA7
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase

/-! # SWn, part 2: the slot, its eighteen numbers, and `tabLen` in registers

The SYM slot `32` of `frontWordsW2` is the unary list of the call numbers `S3.symNums k` (`k = symCallOf …`): the tuple
size `a`, `|FlatSeed|`, then per circuit `j`: `|G_j|`, `tabH G_j`, `tabLen k j = t·(1 + (J+1)(2|G_j|+1)) + 1` (the walk
length `t`, the base list's `J`), the template's length. Here:

* **`swn_word`** (the slot is `unaryList (ofFn (symNums k))`), **`ofFn_symNums`** (the eighteen numbers in order);
* **`tabLen_regs`** (`tabLen k j` in register form), `R7`, `tabLenW` (the flat table's length from registers `L`, `J`,
  `t`), **`tabLen_run`**.

Paper quantities of the main type: the SYM call numbers (P3:3170-3178, list:flatten P3:1508-1520). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (mulStep mulStep_spec mulCost mulCost_le)

/-- **The eighteen call numbers, in order.** -/
theorem ofFn_symNums (k : FinalPass.Seams.SymCall) :
    List.ofFn (PrimT.S3.symNums k) = [k.a, Fintype.card k.Pl.FlatSeed,
      (PrimT.S3.gatesJ k 0).length, (PrimT.S3.gatesJ k 1).length, (PrimT.S3.gatesJ k 2).length,
      (PrimT.S3.gatesJ k 3).length,
      PrimT.tabH (PrimT.S3.gatesJ k 0), PrimT.tabH (PrimT.S3.gatesJ k 1), PrimT.tabH (PrimT.S3.gatesJ k 2),
      PrimT.tabH (PrimT.S3.gatesJ k 3),
      PrimT.S3.tabLen k 0, PrimT.S3.tabLen k 1, PrimT.S3.tabLen k 2, PrimT.S3.tabLen k 3,
      (PrimT.S3.templJ k 0).length, (PrimT.S3.templJ k 1).length, (PrimT.S3.templJ k 2).length,
      (PrimT.S3.templJ k 3).length] := by
  simp only [List.ofFn_succ, List.ofFn_zero]
  rfl

section Link

end Link

/-- **The table length in `tabLenW`'s form**: `tabLen k j = ((2|G_j|+1)(J+1)+1)·t + 1` (`flatTable_len`). -/
theorem tabLen_regs (k : FinalPass.Seams.SymCall) (j : Fin 4) :
    PrimT.S3.tabLen k j = ((2 * (PrimT.S3.gatesJ k j).length + 1) * (k.Pl.base.J + 1) + 1) * k.Pl.walkLen + 1 := by
  rw [show PrimT.S3.tabLen k j = _ from PrimT.S3.flatTable_len _ _ _]
  ring

/-- The flat table length's registers: `(T, U, t2, t3, t4, t5)` for `mulStep`, plus a copy temp. -/
def R7 : Fin 6 ↪ Fin LNR := ⟨![⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩,
  ⟨124, by decide⟩, ⟨125, by decide⟩], by decide⟩

/-- The copy temp. -/
def rC7 : Fin LNR := ⟨126, by decide⟩

/-- **The flat table's length** `T := ((2L+1)(J+1)+1)·t + 1` from `L`, `J`, `t` (kept). -/
def tabLenW {ns : ℕ} (RL RJ RW : Fin LNR) : WM ns LNR :=
  .seq (addK RL (R7 0) rC7 2) (.seq (.inc (R7 0)) (.seq (FinalPass.Hash4.wcopyR RJ (R7 1) rC7) (.seq (.inc (R7 1))
    (.seq (mulStep R7) (.seq (.inc (R7 0)) (.seq (WM.clear (R7 1)) (.seq (FinalPass.Hash4.wcopyR RW (R7 1) rC7)
    (.seq (mulStep R7) (.seq (.inc (R7 0)) (WM.clear (R7 1)))))))))))

theorem r7_val (i : Fin 6) : (R7 i).val = 120 + i.val := by fin_cases i <;> rfl

/-- A register outside `120..126` is none of `tabLenW`'s scratch registers. -/
theorem r7_ne (q : Fin LNR) (hq : q.val < 120 ∨ 127 ≤ q.val) (i : Fin 6) : q ≠ R7 i ∧ q ≠ rC7 := by
  have hv := r7_val i
  have hi := i.isLt
  have hc : rC7.val = 126 := rfl
  exact ⟨fun e => by have := congrArg Fin.val e; omega, fun e => by have := congrArg Fin.val e; omega⟩

/-- The flat table length program's steps. -/
theorem tabLen_cost (L J Wl B1 m1 m2 : ℕ) (hB1 : B1 = (2 * L + 1) * (J + 1))
    (h1 : m1 ≤ 60 * (2 * L + 1 + 1) * (J + 1 + 1)) (h2 : m2 ≤ 60 * (B1 + 1 + 1) * (Wl + 1)) :
    36 * L + 21 * J + 21 * Wl + m1 + m2 + 50 ≤ 400 * (L + J + Wl + 2) ^ 3 := by
  obtain ⟨Y, hY⟩ : ∃ v, v = L + J + Wl + 2 := ⟨_, rfl⟩
  have hY2 : 2 ≤ Y := by omega
  have a0 : (2 * L + 1 + 1) * (J + 1 + 1) ≤ (2 * Y) * Y := Nat.mul_le_mul (by omega) (by omega)
  have e0 : (2 * Y) * Y = 2 * (Y * Y) := by ring
  have a2 : B1 + 1 + 1 ≤ (2 * L + 1 + 1) * (J + 1 + 1) := by
    have e : (2 * L + 1 + 1) * (J + 1 + 1) = (2 * L + 1) * (J + 1) + 2 * L + J + 3 := by ring
    rw [e, ← hB1]
    omega
  have a1 : B1 + 1 + 1 ≤ 2 * (Y * Y) := by omega
  have a3 : (B1 + 1 + 1) * (Wl + 1) ≤ (2 * (Y * Y)) * Y := Nat.mul_le_mul a1 (by omega)
  have e3 : (2 * (Y * Y)) * Y = 2 * (Y * Y * Y) := by ring
  have f1 : 60 * (2 * L + 1 + 1) * (J + 1 + 1) = 60 * ((2 * L + 1 + 1) * (J + 1 + 1)) := by ring
  have f2 : 60 * (B1 + 1 + 1) * (Wl + 1) = 60 * ((B1 + 1 + 1) * (Wl + 1)) := by ring
  have b1 : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
  have b2 : Y * Y ≤ Y * Y * Y := Nat.le_mul_of_pos_right _ (by omega)
  have b5 : (L + J + Wl + 2) ^ 3 = Y * Y * Y := by rw [← hY]; ring
  rw [b5]
  omega

/-- **`tabLenW` computes the flat table's length** into `R7 0`, every other register kept. -/
theorem tabLen_run {ns : ℕ} (cap : ℕ) (RL RJ RW : Fin LNR) (hL : RL.val < 120 ∨ 127 ≤ RL.val)
    (hJ : RJ.val < 120 ∨ 127 ≤ RJ.val) (hWv : RW.val < 120 ∨ 127 ≤ RW.val)
    (σ : WState ns LNR) (L J Wl : ℕ) (vL : σ.val RL = L) (vJ : σ.val RJ = J) (vW : σ.val RW = Wl)
    (hz : ∀ q : Fin LNR, 120 ≤ q.val → q.val ≤ 126 → σ.val q = 0)
    (hc : ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) + L + J + 2 ≤ cap) :
    ∃ c, WExec cap (tabLenW RL RJ RW) σ (σ.setv (R7 0) (((2 * L + 1) * (J + 1) + 1) * Wl + 1)) c ∧
      c ≤ 400 * (L + J + Wl + 2) ^ 3 := by
  obtain ⟨B1, hB1⟩ : ∃ v, v = (2 * L + 1) * (J + 1) := ⟨_, rfl⟩
  rw [← hB1]
  rw [← hB1] at hc
  -- the arithmetic side conditions
  have k1 : (B1 + 1) * (Wl + 1) = (B1 + 1) * Wl + B1 + 1 := by ring
  have k2 : Wl ≤ (B1 + 1) * Wl := Nat.le_mul_of_pos_left _ (by omega)
  have k3 : J + 1 ≤ B1 := by rw [hB1]; exact Nat.le_mul_of_pos_left _ (by omega)
  have k4 : 2 * L + 1 ≤ B1 := by rw [hB1]; exact Nat.le_mul_of_pos_right _ (by omega)
  have gL : L ≤ cap := by omega
  have g2L : 0 + 2 * L ≤ cap := by omega
  have g2Ll : 2 * L < cap := by omega
  have gJ : J ≤ cap := by omega
  have gJl : J < cap := by omega
  have gB : B1 ≤ cap := by omega
  have g2L1 : 2 * L + 1 ≤ cap := by omega
  have gJ1 : J + 1 ≤ cap := by omega
  have gBl : B1 < cap := by omega
  have gW : Wl ≤ cap := by omega
  have gBW : (B1 + 1) * Wl ≤ cap := by omega
  have gB1 : B1 + 1 ≤ cap := by omega
  have gBWl : (B1 + 1) * Wl < cap := by omega
  have v0 := r7_val 0
  have v1 := r7_val 1
  have vc : rC7.val = 126 := rfl
  have z0 : σ.val (R7 0) = 0 := hz _ (by omega) (by omega)
  have z1 : σ.val (R7 1) = 0 := hz _ (by omega) (by omega)
  have zc : σ.val rC7 = 0 := hz _ (by omega) (by omega)
  have zt : ∀ i : Fin 6, 2 ≤ i.val → σ.val (R7 i) = 0 := fun i _ => by
    have hv := r7_val i
    have := i.isLt
    exact hz _ (by omega) (by omega)
  -- the scratch registers' distinctness (no arithmetic below this point)
  obtain ⟨nL0, nLc⟩ := r7_ne RL hL 0
  obtain ⟨nJ1, nJc⟩ := r7_ne RJ hJ 1
  obtain ⟨nJ0, -⟩ := r7_ne RJ hJ 0
  obtain ⟨nW1, nWc⟩ := r7_ne RW hWv 1
  obtain ⟨nW0, -⟩ := r7_ne RW hWv 0
  have n0c : R7 0 ≠ rC7 := fun e => absurd (congrArg Fin.val e) (by rw [v0, vc]; decide)
  have n1c : R7 1 ≠ rC7 := fun e => absurd (congrArg Fin.val e) (by rw [v1, vc]; decide)
  have n01 : R7 0 ≠ R7 1 := R7.injective.ne (by decide)
  -- 1, 2: `T := 2L + 1`
  have e1 := addK_spec cap RL (R7 0) rC7 nL0 nLc n0c 2 σ zc (by rw [vL]; exact gL) (by rw [vL, z0]; exact g2L)
  rw [vL, z0, Nat.zero_add] at e1
  have e2 := WExec.inc (cap := cap) (R7 0) (σ.setv (R7 0) (2 * L))
    (by simp only [WState.setv_val, Function.update_self]; exact g2Ll)
  simp only [WState.setv_val, Function.update_self] at e2
  rw [wsetv_setv] at e2
  -- 3, 4: `U := J + 1`
  have e3 := FinalPass.Hash4.wcopyR_spec cap RJ (R7 1) rC7 nJ1 nJc n1c (σ.setv (R7 0) (2 * L + 1))
    (by simp only [WState.setv_val, Function.update_of_ne n01.symm]; exact z1)
    (by simp only [WState.setv_val, Function.update_of_ne n0c.symm]; exact zc)
    (by simp only [WState.setv_val, Function.update_of_ne nJ0, vJ]; exact gJ)
  rw [show (σ.setv (R7 0) (2 * L + 1)).val RJ = J by
    simp only [WState.setv_val, Function.update_of_ne nJ0, vJ]] at e3
  have e4 := WExec.inc (cap := cap) (R7 1) ((σ.setv (R7 0) (2 * L + 1)).setv (R7 1) J)
    (by simp only [WState.setv_val, Function.update_self]; exact gJl)
  simp only [WState.setv_val, Function.update_self] at e4
  rw [wsetv_setv] at e4
  -- 5, 6: `T := B1 + 1`
  obtain ⟨σ4, h4⟩ : ∃ s, s = (σ.setv (R7 0) (2 * L + 1)).setv (R7 1) (J + 1) := ⟨_, rfl⟩
  rw [← h4] at e4
  have w40 : σ4.val (R7 0) = 2 * L + 1 := by
    rw [h4]; simp only [WState.setv_val, Function.update_of_ne n01, Function.update_self]
  have w41 : σ4.val (R7 1) = J + 1 := by
    rw [h4]; simp only [WState.setv_val, Function.update_self]
  have w4t : ∀ i : Fin 6, 2 ≤ i.val → σ4.val (R7 i) = 0 := fun i hi => by
    have a0 : R7 i ≠ R7 0 := R7.injective.ne (by rintro rfl; exact absurd hi (by decide))
    have a1 : R7 i ≠ R7 1 := R7.injective.ne (by rintro rfl; exact absurd hi (by decide))
    rw [h4]; simp only [WState.setv_val, Function.update_of_ne a0, Function.update_of_ne a1]; exact zt i hi
  have e5 := mulStep_spec cap R7 σ4 (w4t 2 (by decide)) (w4t 3 (by decide)) (w4t 4 (by decide))
    (w4t 5 (by decide)) (by rw [w40, w41, ← hB1]; exact gB) (by rw [w40]; exact g2L1) (by rw [w41]; exact gJ1)
  rw [w40, w41, ← hB1] at e5
  have m1 := mulCost_le (2 * L + 1) (J + 1) (2 * L + 1) le_rfl
  have e6 := WExec.inc (cap := cap) (R7 0) (σ4.setv (R7 0) B1)
    (by simp only [WState.setv_val, Function.update_self]; exact gBl)
  simp only [WState.setv_val, Function.update_self] at e6
  rw [wsetv_setv] at e6
  -- 7: `U := 0`
  have e7 := wclear_spec cap (R7 1) (J + 1) (σ4.setv (R7 0) (B1 + 1))
    (by simp only [WState.setv_val, Function.update_of_ne n01.symm]; exact w41)
    (by simp only [WState.setv_val, Function.update_of_ne n01.symm]; rw [w41]; exact gJ1)
  -- 8: `U := Wl`
  have e8 := FinalPass.Hash4.wcopyR_spec cap RW (R7 1) rC7 nW1 nWc n1c ((σ4.setv (R7 0) (B1 + 1)).setv (R7 1) 0)
    (by simp only [WState.setv_val, Function.update_self])
    (by rw [h4]; simp only [WState.setv_val, Function.update_of_ne n1c.symm, Function.update_of_ne n0c.symm]
        exact zc)
    (by rw [h4]; simp only [WState.setv_val, Function.update_of_ne nW1, Function.update_of_ne nW0, vW]; exact gW)
  rw [show ((σ4.setv (R7 0) (B1 + 1)).setv (R7 1) 0).val RW = Wl by
    rw [h4]; simp only [WState.setv_val, Function.update_of_ne nW1, Function.update_of_ne nW0, vW]] at e8
  rw [wsetv_setv] at e8
  -- 9, 10: `T := (B1+1)·Wl + 1`
  obtain ⟨σ8, h8⟩ : ∃ s, s = (σ4.setv (R7 0) (B1 + 1)).setv (R7 1) Wl := ⟨_, rfl⟩
  rw [← h8] at e8
  have w80 : σ8.val (R7 0) = B1 + 1 := by
    rw [h8]; simp only [WState.setv_val, Function.update_of_ne n01, Function.update_self]
  have w81 : σ8.val (R7 1) = Wl := by
    rw [h8]; simp only [WState.setv_val, Function.update_self]
  have w8t : ∀ i : Fin 6, 2 ≤ i.val → σ8.val (R7 i) = 0 := fun i hi => by
    have a0 : R7 i ≠ R7 0 := R7.injective.ne (by rintro rfl; exact absurd hi (by decide))
    have a1 : R7 i ≠ R7 1 := R7.injective.ne (by rintro rfl; exact absurd hi (by decide))
    rw [h8]; simp only [WState.setv_val, Function.update_of_ne a0, Function.update_of_ne a1]; exact w4t i hi
  have e9 := mulStep_spec cap R7 σ8 (w8t 2 (by decide)) (w8t 3 (by decide)) (w8t 4 (by decide))
    (w8t 5 (by decide)) (by rw [w80, w81]; exact gBW) (by rw [w80]; exact gB1) (by rw [w81]; exact gW)
  rw [w80, w81] at e9
  have m2 := mulCost_le (B1 + 1) Wl (B1 + 1) le_rfl
  have e10 := WExec.inc (cap := cap) (R7 0) (σ8.setv (R7 0) ((B1 + 1) * Wl))
    (by simp only [WState.setv_val, Function.update_self]; exact gBWl)
  simp only [WState.setv_val, Function.update_self] at e10
  rw [wsetv_setv] at e10
  -- 11: `U := 0`
  have e11 := wclear_spec cap (R7 1) Wl (σ8.setv (R7 0) ((B1 + 1) * Wl + 1))
    (by simp only [WState.setv_val, Function.update_of_ne n01.symm]; exact w81)
    (by simp only [WState.setv_val, Function.update_of_ne n01.symm]; rw [w81]; exact gW)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11)))))))))) ?_ le_rfl, ?_⟩
  · rw [h8, h4]
    refine WState.eq rfl rfl ?_ rfl
    funext q
    simp only [WState.setv_val]
    by_cases a1 : q = R7 1
    · subst a1
      simp only [Function.update_self, Function.update_of_ne n01.symm, z1]
    · by_cases a0 : q = R7 0
      · subst a0
        simp only [Function.update_self, Function.update_of_ne n01]
      · simp only [Function.update_of_ne a1, Function.update_of_ne a0]
  · clear nL0 nLc nJ1 nJc nJ0 nW1 nWc nW0 n0c n1c n01
    have := tabLen_cost L J Wl B1 _ _ hB1 m1 m2
    omega

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
