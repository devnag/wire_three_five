import Proof.Wire_3_5.Primitive.SeedFix.C4KWq
import Proof.Wire_3_5.Primitive.SeedFix.C4KWg

/-! # C4KW, part 17: stage B2's setup (the counts, `s = ⌊√(t·B*)⌋`, the width, the words)

From the stage's entry (`1^t, 1^J, 1^{B*}` on streams `1 2 3`): the counts into registers, `s` (C6's `sqrtF`), `2t`,
the width `wd = J·2t·Wmax + 1` (`Wmax = 16t + 20(s+2)`, every weight below `2^wd`: **`pow_lt_wd`**), the words
`P = C = 0` of width `wd` (X1's `binW`), and the level count `J + 1` (**`setup_run`**).

Paper quantity of the main type: the width of the cleared weights' binary words (P3:2280-2281). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.UnionMachine.EwLevel (twW twW_spec twOf twMax twOf_le twCost)

/-- `r += k`. -/
def incN (r : Fin 48) : ℕ → WM 5 48
  | 0 => .skip
  | k + 1 => .seq (.inc r) (incN r k)

theorem incN_spec (cap : ℕ) (r : Fin 48) : ∀ (k : ℕ) (σ : WState 5 48), σ.val r + k ≤ cap →
    WExec cap (incN r k) σ (σ.setv r (σ.val r + k)) (4 * k)
  | 0, σ, _ => by rw [Nat.add_zero, wsetv_same]; exact WExec.skip σ
  | k + 1, σ, h => by
    have t1 := WExec.inc (cap := cap) r σ (by omega)
    have t2 := incN_spec cap r k (σ.setv r (σ.val r + 1)) (by simp; omega)
    rw [wsetv_setv] at t2
    simp only [wsetv_val_self] at t2
    exact WExec.mono (WExec.seq t1 (by rw [show σ.val r + (k + 1) = σ.val r + 1 + k by ring]; exact t2)) (by omega)

/-- The square root's registers. -/
def Rq : Fin 7 ↪ Fin 48 := ⟨![20, 1, 21, 22, 23, 24, 25], by decide⟩
/-- The binary writer's registers (value `26 = 0`, width `27`). -/
def Rg : Fin 8 → Fin 48 := ![26, 27, 28, 29, 30, 31, 32, 33]

theorem Rg_inj : Function.Injective Rg := by decide

/-- The width. -/
def wdOf (t s J : ℕ) : ℕ := J * (2 * t) * twMax t s + 1

theorem pow_lt_wd (t s J : ℕ) : twMax t s ^ (2 * t * J) < 2 ^ wdOf t s J := by
  have h1 : twMax t s ^ (2 * t * J) ≤ (2 ^ twMax t s) ^ (2 * t * J) :=
    Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  rw [← pow_mul] at h1
  refine lt_of_le_of_lt h1 (Nat.pow_lt_pow_right (by norm_num) ?_)
  unfold wdOf; nlinarith

theorem rep_rd (a : ℕ) : (∀ q, q < a → readTapeBit (List.replicate a true) q = true) ∧
    readTapeBit (List.replicate a true) a = false := by
  refine ⟨fun q hq => ?_, ?_⟩
  · simp only [readTapeBit]; rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  · simp [readTapeBit]

/-- The setup's capacity need. -/
def capB (t s J B : ℕ) : ℕ :=
  2 * (B * t + 2) * (B * t + 2) + 2 ^ (J + 1) + 1100 * (t + s + J + 2) + 4 * wdOf t s J + 2 * twMax t s + 2 * B +
    B * t + 100

/-- B2's setup, part A: the counts and the square root. -/
def setupA : WM 5 48 := .seq (cntW 1 (Vr 0)) (.seq (cntW 2 rJ) (.seq (cntW 3 rB) (.seq (UnionMachine.FsKit.mulR (Vr 0) rB 20 rT rU) (.seq (.inc 20) (.seq (UnionMachine.EwKit.sqrtF Rq) ((WM.clear 20)))))))
/-- Part B: `2t`, `Wmax`, the width. -/
def setupB : WM 5 48 := .seq (UnionMachine.FsKit.mulK (Vr 0) rt2 rT 2) (.seq (UnionMachine.FsKit.mulK (Vr 0) 21 rT 16) (.seq (UnionMachine.FsKit.mulK (Vr 1) 21 rT 20) (.seq (incN 21 40) (.seq (UnionMachine.FsKit.mulR rt2 rJ 22 rT rU) (.seq (UnionMachine.FsKit.mulR 21 22 27 rT rU) (.seq (.inc 27) (.seq (WM.clear 21) ((WM.clear 22)))))))))
/-- Part C: the words and the level count. -/
def setupC : WM 5 48 := .seq (UnionMachine.BinW.binW sP Rg) (.seq (UnionMachine.BinW.binW sC Rg) (.seq (UnionMachine.BinW.dupR rJ rL rT) ((.inc rL))))
/-- **B2's setup.** -/
def setupW : WM 5 48 := .seq setupA (.seq setupB setupC)

def costA (t J B : ℕ) : ℕ := (7 * t + 1) + 1 + ((7 * J + 1) + 1 + ((7 * B + 1) + 1 + ((18 * B + 3 + 1 + (B * (18 * t + 7) + 1)) + 1 + (3 + 1 + ((1000 * (B * t + 2) * (B * t + 2) * (B * t + 2)) + 1 + ((3 * (B * t + 1) + 1)))))))
def costB (t s J : ℕ) : ℕ := (2 * (18 * t + 4)) + 1 + ((16 * (18 * t + 4)) + 1 + ((20 * (18 * s + 4)) + 1 + ((4 * 40) + 1 + ((18 * J + 3 + 1 + (J * (18 * (2 * t) + 7) + 1)) + 1 + ((18 * (J * (2 * t)) + 3 + 1 + (J * (2 * t) * (18 * twMax t s + 7) + 1)) + 1 + (3 + 1 + ((3 * twMax t s + 1) + 1 + ((3 * (J * (2 * t)) + 1)))))))))
def costC (t s J : ℕ) : ℕ := UnionMachine.BinW.binCost 0 (wdOf t s J) + 1 + (UnionMachine.BinW.binCost 0 (wdOf t s J) + 1 + ((18 * J + 3) + 1 + (3)))

/-- The setup's cost. -/
def setupCost (t s J B : ℕ) : ℕ := costA t J B + 1 + (costB t s J + 1 + costC t s J)

theorem Rq0 : Rq 0 = 20 := rfl
theorem Rq1 : Rq 1 = 1 := rfl
theorem Rq2 : Rq 2 = 21 := rfl
theorem Rq3 : Rq 3 = 22 := rfl
theorem Rq4 : Rq 4 = 23 := rfl
theorem Rq5 : Rq 5 = 24 := rfl
theorem Rq6 : Rq 6 = 25 := rfl

/-- Part A's exit (canonical form). -/
def outA (σ0 : WState 5 48) (t J B s : ℕ) : WState 5 48 :=
  (((((((σ0.seth 1 t).seth 2 J).seth 3 B).setv (Vr 0) t).setv rJ J).setv rB B).setv (Vr 1) s)

/-- Part B's exit. -/
def outB (σ0 : WState 5 48) (t J B s : ℕ) : WState 5 48 :=
  ((outA σ0 t J B s).setv rt2 (2 * t)).setv 27 (wdOf t s J)

/-- Part C's exit. -/
def outC (σ0 : WState 5 48) (t J B s : ℕ) : WState 5 48 :=
  (((outB σ0 t J B s).sets sP (frame (binary (wdOf t s J) 0))).sets sC (frame (binary (wdOf t s J) 0))).setv rL (J + 1)

theorem setupA_run (cap : ℕ) (σ0 : WState 5 48) (t J B : ℕ) (hv0 : ∀ r, σ0.val r = 0) (hsh0 : ∀ i, σ0.sh i = 0)
    (hs1 : σ0.st 1 = List.replicate t true) (hs2 : σ0.st 2 = List.replicate J true)
    (hs3 : σ0.st 3 = List.replicate B true) (hcap : capB t (Nat.sqrt (t * B)) J B ≤ cap) :
    WExec cap setupA σ0 (outA σ0 t J B (Nat.sqrt (t * B))) (costA t J B) := by
  set s := Nat.sqrt (t * B) with hs
  have hsq : Nat.sqrt (B * t) = s := by rw [hs, Nat.mul_comm]
  have hbt1 : B * t + 2 ≤ (B * t + 2) * (B * t + 2) := by nlinarith
  have g1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have hcp : 2 * (B * t + 2) * (B * t + 2) + 1000 * (t + s + J + 2) + 2 * B + B * t + 100 ≤ cap := by
    unfold capB at hcap; omega
  obtain ⟨hT1, hF1⟩ := rep_rd t
  obtain ⟨hT2, hF2⟩ := rep_rd J
  obtain ⟨hT3, hF3⟩ := rep_rd B
  have t1 := cnt_loop cap (1 : Fin 6) (Vr 0) _ t hT1 hF1 t σ0 hs1 (by rw [hsh0]; omega) (by rw [hv0]; omega)
  set σ1 := (σ0.seth 1 t).setv (Vr 0) (σ0.val (Vr 0) + t) with hσ1
  have t2 := cnt_loop cap (2 : Fin 6) rJ _ J hT2 hF2 J σ1 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ1, hv0, hs2]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ1, hv0, hsh0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ1, hv0]; try omega)
  set σ2 := (σ1.seth 2 J).setv rJ (σ1.val rJ + J) with hσ2
  have t3 := cnt_loop cap (3 : Fin 6) rB _ B hT3 hF3 B σ2 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ2, hσ1, hv0, hs3]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ2, hσ1, hv0, hsh0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ2, hσ1, hv0]; try omega)
  set σ3 := (σ2.seth 3 B).setv rB (σ2.val rB + B) with hσ3
  have t4 := UnionMachine.FsKit.mulR_spec cap (Vr 0) rB 20 rT rU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) σ3 t B (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ3, hσ2, hσ1, hv0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ3, hσ2, hσ1, hv0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ3, hσ2, hσ1, hv0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ3, hσ2, hσ1, hv0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ3, hσ2, hσ1, hv0]; try omega) (by omega) (by omega)
  set σ4 := σ3.setv 20 (σ3.val 20 + B * t) with hσ4
  have t5 := WExec.inc (cap := cap) 20 σ4 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ4, hσ3, hσ2, hσ1, hv0]; nlinarith)
  set σ5 := σ4.setv 20 (σ4.val 20 + 1) with hσ5
  obtain ⟨n6, t6x, hn6⟩ := UnionMachine.EwKit.sqrtF_spec cap Rq σ5 (B * t) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq0]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq1]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq2]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq3]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq4]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq5]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq6]; try omega) (by nlinarith)
  have t6 := WExec.mono t6x hn6
  set σ6 := σ5.setv (Rq 1) (Nat.sqrt (B * t)) with hσ6
  have t7 := wclear_spec cap 20 (B * t + 1) σ6 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq1]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, Rq1]; nlinarith)
  refine WExec.cast cap (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 (WExec.seq t4 (WExec.seq t5 (WExec.seq t6 (t7))))))) ?_ le_rfl
  clear t1 t2 t3 t4 t5 t6 t6x t7 hn6
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, outA, Rq1]
  · funext i; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, outA, Rq1]
  · funext r; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hv0, outA, Rq1, hsq]
    split_ifs <;> simp_all (config := {decide := true})

theorem setupB_run (cap : ℕ) (σ0 : WState 5 48) (t J B : ℕ) (hv0 : ∀ r, σ0.val r = 0)
    (hcap : capB t (Nat.sqrt (t * B)) J B ≤ cap) :
    WExec cap setupB (outA σ0 t J B (Nat.sqrt (t * B))) (outB σ0 t J B (Nat.sqrt (t * B))) (costB t (Nat.sqrt (t * B)) J) := by
  set s := Nat.sqrt (t * B) with hs
  have hWm : twMax t s = 16 * t + 20 * s + 40 := by unfold twMax; ring
  have hWm1 : 1 ≤ twMax t s := by omega
  have hJt : J * (2 * t) ≤ wdOf t s J := by
    have := Nat.le_mul_of_pos_right (J * (2 * t)) hWm1
    unfold wdOf; omega
  have hwd : wdOf t s J = J * (2 * t) * twMax t s + 1 := rfl
  have g1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have hcp : 1000 * (t + s + J + 2) + 4 * wdOf t s J + 2 * twMax t s + 100 ≤ cap := by
    unfold capB at hcap; omega
  set σ0' := outA σ0 t J B s with hσ0
  have t8 := UnionMachine.FsKit.mulK_spec cap (Vr 0) rt2 rT (by decide) (by decide) (by decide) t 2 σ0' (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA]; try omega) (by omega)
  set σ8 := σ0'.setv rt2 (σ0'.val rt2 + 2 * t) with hσ8
  have t9 := UnionMachine.FsKit.mulK_spec cap (Vr 0) 21 rT (by decide) (by decide) (by decide) t 16 σ8 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ8, hv0, hσ0, outA]; try omega) (by omega)
  set σ9 := σ8.setv 21 (σ8.val 21 + 16 * t) with hσ9
  have t10 := UnionMachine.FsKit.mulK_spec cap (Vr 1) 21 rT (by decide) (by decide) (by decide) s 20 σ9 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by omega)
  set σ10 := σ9.setv 21 (σ9.val 21 + 20 * s) with hσ10
  have t11 := incN_spec cap 21 40 σ10 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega)
  set σ11 := σ10.setv 21 (σ10.val 21 + 40) with hσ11
  have v21 : σ11.val 21 = twMax t s := (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega)
  have t12 := UnionMachine.FsKit.mulR_spec cap rt2 rJ 22 rT rU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) σ11 (2 * t) J (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by omega) (by omega)
  set σ12 := σ11.setv 22 (σ11.val 22 + J * (2 * t)) with hσ12
  have t13 := UnionMachine.FsKit.mulR_spec cap 21 22 27 rT rU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) σ12 (twMax t s) (J * (2 * t)) (by rw [hσ12]; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, v21]) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by omega) (by omega)
  set σ13 := σ12.setv 27 (σ12.val 27 + J * (2 * t) * twMax t s) with hσ13
  have t14 := WExec.inc (cap := cap) 27 σ13 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega)
  set σ14 := σ13.setv 27 (σ13.val 27 + 1) with hσ14
  have t15 := wclear_spec cap 21 (twMax t s) σ14 (by rw [hσ14, hσ13, hσ12]; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, v21]) (by rw [hσ14, hσ13, hσ12]; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, v21]; omega)
  set σ15 := σ14.setv 21 0 with hσ15
  have t16 := wclear_spec cap 22 (J * (2 * t)) σ15 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ15, hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ15, hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hv0, hσ0, outA]; try omega)
  refine WExec.cast cap (WExec.seq t8 (WExec.seq t9 (WExec.seq t10 (WExec.seq t11 (WExec.seq t12 (WExec.seq t13 (WExec.seq t14 (WExec.seq t15 (t16))))))))) ?_ le_rfl
  clear t8 t9 t10 t11 t12 t13 t14 t15 t16
  refine WState.eq rfl rfl ?_ rfl
  funext r; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ15, hσ14, hσ13, hσ12, hσ11, hσ10, hσ9, hσ8, hσ0, outA, outB, hv0, hwd]
  split_ifs <;> simp_all (config := {decide := true})

theorem setupC_run (cap : ℕ) (σ0 : WState 5 48) (t J B : ℕ) (hv0 : ∀ r, σ0.val r = 0) (hsh0 : ∀ i, σ0.sh i = 0)
    (hsP : σ0.st sP = []) (hsC : σ0.st sC = []) (hcap : capB t (Nat.sqrt (t * B)) J B ≤ cap) :
    WExec cap setupC (outB σ0 t J B (Nat.sqrt (t * B))) (outC σ0 t J B (Nat.sqrt (t * B))) (costC t (Nat.sqrt (t * B)) J) := by
  set s := Nat.sqrt (t * B) with hs
  have hwd : wdOf t s J = J * (2 * t) * twMax t s + 1 := rfl
  have g1 : 1 ≤ 2 ^ (J + 1) := Nat.one_le_two_pow
  have hcp : 1000 * (t + s + J + 2) + 4 * wdOf t s J + 100 ≤ cap := by
    unfold capB at hcap; omega
  set σ0' := outB σ0 t J B s with hσ0
  have t17 := UnionMachine.BinW.binW_spec cap sP Rg Rg_inj σ0' 0 (wdOf t s J) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA, outB, hwd, Rg]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA, outB, hwd, Rg]; try omega) (fun j hj => by fin_cases j <;> (try simp at hj) <;> simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ0, outA, outB, hv0, Rg]) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA, outB, hwd, hsP]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hv0, hσ0, outA, outB, hwd, hsh0]; try omega) (by omega)
  set σ17 := σ0'.sets sP (frame (binary (wdOf t s J) 0)) with hσ17
  have t18 := UnionMachine.BinW.binW_spec cap sC Rg Rg_inj σ17 0 (wdOf t s J) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ17, hv0, hσ0, outA, outB, hwd, Rg]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ17, hv0, hσ0, outA, outB, hwd, Rg]; try omega) (fun j hj => by fin_cases j <;> (try simp at hj) <;> simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ17, hσ0, outA, outB, hv0, Rg]) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ17, hv0, hσ0, outA, outB, hwd, hsC]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ17, hv0, hσ0, outA, outB, hwd, hsh0]; try omega) (by omega)
  set σ18 := σ17.sets sC (frame (binary (wdOf t s J) 0)) with hσ18
  have t19 := UnionMachine.BinW.dupR_spec cap rJ rL rT (by decide) (by decide) (by decide) σ18 J (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ18, hσ17, hv0, hσ0, outA, outB, hwd]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ18, hσ17, hv0, hσ0, outA, outB, hwd]; try omega) (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ18, hσ17, hv0, hσ0, outA, outB, hwd]; try omega) (by omega)
  set σ19 := σ18.setv rL J with hσ19
  have t20 := WExec.inc (cap := cap) rL σ19 (by simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ19, hσ18, hσ17, hv0, hσ0, outA, outB, hwd]; try omega)
  refine WExec.cast cap (WExec.seq t17 (WExec.seq t18 (WExec.seq t19 (t20)))) ?_ le_rfl
  clear t17 t18 t19 t20
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ19, hσ18, hσ17, hσ0, outA, outB, outC]
  · funext i; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ19, hσ18, hσ17, hσ0, outA, outB, outC]
  · funext r; simp (config := {decide := true}) [WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply, Vr_apply, hσ19, hσ18, hσ17, hσ0, outA, outB, outC]
    split_ifs <;> simp_all (config := {decide := true})

/-- **B2's setup run.** -/
theorem setup_run (cap : ℕ) (σ0 : WState 5 48) (t J B : ℕ) (hv0 : ∀ r, σ0.val r = 0) (hsh0 : ∀ i, σ0.sh i = 0)
    (hs1 : σ0.st 1 = List.replicate t true) (hs2 : σ0.st 2 = List.replicate J true)
    (hs3 : σ0.st 3 = List.replicate B true) (hsP : σ0.st sP = []) (hsC : σ0.st sC = [])
    (hcap : capB t (Nat.sqrt (t * B)) J B ≤ cap) :
    WExec cap setupW σ0 (outC σ0 t J B (Nat.sqrt (t * B))) (setupCost t (Nat.sqrt (t * B)) J B) :=
  WExec.seq (setupA_run cap σ0 t J B hv0 hsh0 hs1 hs2 hs3 hcap)
    (WExec.seq (setupB_run cap σ0 t J B hv0 hcap) (setupC_run cap σ0 t J B hv0 hsh0 hsP hsC hcap))

end NearCubicWires.WireExponent3_5.PrimT.C4KW.B2
