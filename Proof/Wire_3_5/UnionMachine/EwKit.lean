import Proof.Wire_3_5.UnionMachine.FsKit
import Proof.Wire_3_5.Primitive.Writers.UnaryPow

/-! # C6, e/W_j, part 1: comparison flags and the integer square root

The fixed hash's level windows `W_j = 16t + 20(⌊√(t·B_*)⌋ + 1)/2^{⌊j/2⌋} + 20` (filt:majorant, P3:2150-2157;
`Filters.MajorantParams.W`) need `⌊√(t·B_*)⌋` in a register. Exact final states, costs in the values (the stage's
cost bound is polynomial in the call's numbers, not in the capacity):
* **`subR_spec`** (`D -= X`, truncated, `X` kept), **`leF_spec`** (`F := [A ≤ B]`, both kept);
* **`sqrtF_spec`**: `K := ⌊√x⌋` from `X = x` (kept), by `k ↦ k + 1` while `(k+1)² ≤ x` (`Nat.eq_sqrt`).

Paper quantity: `⌊√(t·B_*)⌋` of the fixed hash's windows (filt:majorant). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR dupL_spec bsetv_self)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Truncated subtraction -/

/-- The subtraction loop: `D -= T`, `T := 0` (truncated). -/
def subL (T D : Fin nr) : WM ns nr := .whr T (.seq (.dec T) (.dec D))

theorem subL_spec (T D : Fin nr) (hTD : T ≠ D) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val T = n → σ.val T ≤ cap → σ.val D ≤ cap →
      WExec cap (subL T D) σ ((σ.setv T 0).setv D (σ.val D - n)) (5 * n + 1)
  | 0, σ, h0, _, _ => by
    rw [Nat.sub_zero, bsetv_self σ T 0 h0, wsetv_same]
    exact WExec.whrF h0
  | n + 1, σ, hn, hT, hD => by
    have h1 := WExec.dec (cap := cap) T σ hT
    have h2 := WExec.dec (cap := cap) D (σ.setv T (σ.val T - 1)) (by simp [Ne.symm hTD]; omega)
    have ih := subL_spec T D hTD n ((σ.setv T (σ.val T - 1)).setv D ((σ.setv T (σ.val T - 1)).val D - 1))
      (by simp [hTD]; omega) (by simp [hTD]; omega) (by simp [Ne.symm hTD]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) ih) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases hjD : j = D
      · subst hjD; simp [Ne.symm hTD] <;> omega
      · by_cases hjT : j = T
        · subst hjT; simp [hjD]
        · simp [hjD, hjT]
    · rfl

/-- **`D -= X`** (truncated; `X` kept, scratch `T`, `U` at `0`). -/
def subR (X D T U : Fin nr) : WM ns nr := .seq (dupR X T U) (subL T D)

theorem subR_spec (X D T U : Fin nr) (hXD : X ≠ D) (hXT : X ≠ T) (hXU : X ≠ U) (hDT : D ≠ T) (hDU : D ≠ U)
    (hTU : T ≠ U) (σ : WState ns nr) (x : ℕ) (hx : σ.val X = x) (ht : σ.val T = 0) (hu : σ.val U = 0)
    (hcx : x ≤ cap) (hcd : σ.val D ≤ cap) :
    WExec cap (subR X D T U) σ (σ.setv D (σ.val D - x)) (18 * x + 3 + 1 + (5 * x + 1)) := by
  have h1 := BinW.dupR_spec cap X T U hXT hXU hTU σ x hx ht hu hcx
  have h2 := subL_spec cap T D (Ne.symm hDT) x (σ.setv T x) (by simp) (by simp; omega)
    (by simp [hDT]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j
    simp only [WState.setv_val, Function.update_apply]
    by_cases hjD : j = D
    · subst hjD; simp [hDT]
    · by_cases hjT : j = T
      · subst hjT; simp [hjD, ht]
      · simp [hjD, hjT]
  · rfl

/-! ## The integer square root -/

/-- `gtFlagW`'s registers inside the square root's: `(X1, S, F, t, u, w)`. -/
def gR : Fin 6 ↪ Fin 7 := ⟨![0, 2, 3, 4, 5, 6], by decide⟩

@[simp] theorem gR_apply (i : Fin 6) : gR i = ![0, 2, 3, 4, 5, 6] i := rfl

section Sqrt
variable (R : Fin 7 ↪ Fin nr)

/-- One round: `F := 0`, `K := K + 1`, `S := S + 2K + 1` (`= (K+1)²`), `F := [S < X1]`. -/
def sqBody : WM ns nr :=
  .seq (.seq (.seq (.seq (.seq (.dec (R 3)) (.inc (R 1))) (dupR (R 1) (R 2) (R 4))) (dupR (R 1) (R 2) (R 4)))
    (.inc (R 2))) (PrimAsm.UnaryArith.gtFlagW (gR.trans R))

/-- **`K := ⌊√x⌋`** from `X1 = x + 1` (kept): `S := 1`, `F := [S < X1]`, rounds while `F`, then `S := 0`. -/
def sqrtF : WM ns nr :=
  .seq (.inc (R 2)) (.seq (PrimAsm.UnaryArith.gtFlagW (gR.trans R)) (.seq (.whr (R 3) (sqBody R)) (WM.clear (R 2))))

/-- The state after `k` rounds. -/
def stQ (σ : WState ns nr) (x k : ℕ) : WState ns nr :=
  ((σ.setv (R 1) k).setv (R 2) ((k + 1) * (k + 1))).setv (R 3) (if (k + 1) * (k + 1) < x + 1 then 1 else 0)

theorem sqBody_spec (σ : WState ns nr) (x k : ℕ) (hx : σ.val (R 0) = x + 1) (h4 : σ.val (R 4) = 0)
    (h5 : σ.val (R 5) = 0) (h6 : σ.val (R 6) = 0) (hk : (k + 1) * (k + 1) ≤ x) (hcap : 2 * (x + 2) * (x + 2) ≤ cap) :
    WExec cap (sqBody R) (stQ R σ x k) (stQ R σ x (k + 1)) (200 * (x + 2) * (x + 2)) := by
  have hne : ∀ {i j : Fin 7}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hR : ∀ i j : Fin 7, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have hk1 : k + 1 ≤ x := by nlinarith
  have hsq : (k + 1) * (k + 1) + (k + 1) + (k + 1) + 1 = (k + 1 + 1) * (k + 1 + 1) := by ring
  have hsq2 : (k + 1 + 1) * (k + 1 + 1) ≤ 2 * (x + 2) * (x + 2) := by nlinarith
  have hc1 : 1 ≤ cap := by nlinarith
  have hxc : x + 2 ≤ cap := by nlinarith
  have c1 := WExec.dec (cap := cap) (R 3) (stQ R σ x k) (by simp [stQ, hR]; split_ifs <;> omega)
  have c2 := WExec.seq c1 (WExec.inc (cap := cap) (R 1) _ (by simp [stQ, hR]; omega))
  have c3 := WExec.seq c2 (FsKit.addR_spec cap (R 1) (R 2) (R 4) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ (k + 1) (by simp [stQ, hR]) (by simp [stQ, hR, h4]) (by simp [stQ, hR]; nlinarith)
    (by omega))
  have c4 := WExec.seq c3 (FsKit.addR_spec cap (R 1) (R 2) (R 4) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ (k + 1) (by simp [stQ, hR]) (by simp [stQ, hR, h4]) (by simp [stQ, hR]; nlinarith)
    (by omega))
  have c5 := WExec.seq c4 (WExec.inc (cap := cap) (R 2) _ (by simp [stQ, hR]; nlinarith))
  have c6 := WExec.seq c5 (PrimAsm.UnaryArith.gtFlagW_spec cap (gR.trans R) _ (by simp [stQ, hR, hk])
    (by simp [stQ, hR, h4]) (by simp [stQ, hR, h5]) (by simp [stQ, hR, h6]) (by simp [stQ, hR, hx]; omega)
    (by simp [stQ, hR]; nlinarith) hc1)
  refine WExec.cast cap c6 ?_ ?_
  · apply WState.eq
    · simp [stQ]
    · simp [stQ]
    · funext j
      by_cases j3 : j = R 3
      · subst j3; simp [stQ, hR, hx, hsq]
      · by_cases j2 : j = R 2
        · subst j2; simp [stQ, hR]; ring
        · by_cases j1 : j = R 1
          · subst j1; simp [stQ, hR]
          · simp [stQ, Function.update_apply, j1, j2, j3]
    · simp [stQ]
  · simp [stQ, hR, hx]
    nlinarith

/-- **The integer square root**: `K := ⌊√x⌋` from `X1 = x + 1` (kept), the scratch back at `0`. -/
theorem sqrtF_spec (σ : WState ns nr) (x : ℕ) (hx : σ.val (R 0) = x + 1) (h1 : σ.val (R 1) = 0)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (h5 : σ.val (R 5) = 0)
    (h6 : σ.val (R 6) = 0) (hcap : 2 * (x + 2) * (x + 2) ≤ cap) :
    ∃ n, WExec cap (sqrtF R) σ (σ.setv (R 1) (Nat.sqrt x)) n ∧ n ≤ 1000 * (x + 2) * (x + 2) * (x + 2) := by
  have hR : ∀ i j : Fin 7, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have hc1 : 1 ≤ cap := by nlinarith
  have hxc : x + 2 ≤ cap := by nlinarith
  have e1 := WExec.inc (cap := cap) (R 2) σ (by rw [h2]; omega)
  have e2 := PrimAsm.UnaryArith.gtFlagW_spec cap (gR.trans R) (σ.setv (R 2) (σ.val (R 2) + 1)) (by simp [hR, h3])
    (by simp [hR, h4]) (by simp [hR, h5]) (by simp [hR, h6]) (by simp [hR, hx]; omega) (by simp [hR, h2]; omega) hc1
  have e0 : (σ.setv (R 2) (σ.val (R 2) + 1)).setv ((gR.trans R) 2)
      (if (σ.setv (R 2) (σ.val (R 2) + 1)).val ((gR.trans R) 1) < (σ.setv (R 2) (σ.val (R 2) + 1)).val ((gR.trans R) 0)
        then 1 else 0) = stQ R σ x 0 := by
    apply WState.eq
    · simp [stQ]
    · simp [stQ]
    · funext j
      by_cases j3 : j = R 3
      · subst j3; simp [stQ, hR, hx, h2]
      · by_cases j2 : j = R 2
        · subst j2; simp [stQ, hR, h2]
        · by_cases j1 : j = R 1
          · subst j1; simp [stQ, hR, h1]
          · simp [stQ, Function.update_apply, j1, j2, j3]
    · simp [stQ]
  rw [e0] at e2
  have e3 := PrimAsm.UnaryPow.flagLoop cap (R 3) (sqBody R) (200 * (x + 2) * (x + 2)) (Nat.sqrt x) (stQ R σ x)
    (fun k hk => by
      have : (k + 1) * (k + 1) ≤ x := Nat.le_sqrt.mp hk
      simp [stQ, hR]; omega)
    (by
      have : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
      simp [stQ, hR]; omega)
    (fun k hk => sqBody_spec cap R σ x k hx h4 h5 h6 (Nat.le_sqrt.mp hk) hcap)
  have hm : Nat.sqrt x ≤ x := Nat.sqrt_le_self x
  have hm2 : (Nat.sqrt x + 1) * (Nat.sqrt x + 1) ≤ 2 * (x + 2) * (x + 2) := by nlinarith
  have e4 := wclear_spec cap (R 2) ((Nat.sqrt x + 1) * (Nat.sqrt x + 1)) (stQ R σ x (Nat.sqrt x))
    (by simp [stQ, hR]) (by simp [stQ, hR]; omega)
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · simp [stQ]
    · simp [stQ]
    · funext j
      have hst : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
      by_cases j3 : j = R 3
      · subst j3; simp [stQ, hR, h3]; omega
      · by_cases j2 : j = R 2
        · subst j2; simp [stQ, hR, h2]
        · by_cases j1 : j = R 1
          · subst j1; simp [stQ, hR]
          · simp [stQ, Function.update_apply, j1, j2, j3]
    · simp [stQ]
  · have v0 : (σ.setv (R 2) (σ.val (R 2) + 1)).val ((gR.trans R) 0) = x + 1 := by simp [hR, hx]
    have v1 : (σ.setv (R 2) (σ.val (R 2) + 1)).val ((gR.trans R) 1) = 1 := by simp [hR, h2]
    rw [v0, v1]
    have hp := Nat.mul_le_mul hm (le_refl (200 * (x + 2) * (x + 2) + 2))
    nlinarith

end Sqrt

/-! ## The window's power `2^{⌈log₂(2w+1)⌉}` -/

theorem pow_clog_le2 (x : ℕ) (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases Nat.lt_or_ge x 2 with h | h
  · have : x = 1 := by omega
    subst this; simp
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := x) (by omega)
    rw [Nat.pred_eq_sub_one] at h1
    have h2 : 0 < Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
    have e : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

section Pow
variable (R : Fin 5 ↪ Fin nr)

/-- One doubling: `D -= P` (truncated), `P := 2P`. -/
def pwBody : WM ns nr := .seq (.seq (subR (R 1) (R 2) (R 3) (R 4)) (dupR (R 1) (R 3) (R 4))) (WM.move (R 3) (R 1))

/-- **`P := 2^{⌈log₂(2w+1)⌉}`** from `W = w` (kept): `P := 1`, `D := 2w`, doublings while `D ≠ 0`. -/
def powF : WM ns nr :=
  .seq (.seq (.seq (.inc (R 1)) (dupR (R 0) (R 2) (R 3))) (dupR (R 0) (R 2) (R 3))) (.whr (R 2) (pwBody R))

/-- The state after `i` doublings. -/
def stP (σ : WState ns nr) (w i : ℕ) : WState ns nr := (σ.setv (R 1) (2 ^ i)).setv (R 2) (2 * w + 1 - 2 ^ i)

theorem pwBody_spec (σ : WState ns nr) (w i : ℕ) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0)
    (hi : 2 ^ i < 2 * w + 1) (hcap : 8 * w + 8 ≤ cap) :
    WExec cap (pwBody R) (stP R σ w i) (stP R σ w (i + 1)) (60 * (2 * w + 2)) := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hR : ∀ i j : Fin 5, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have hp1 := Nat.one_le_two_pow (n := i)
  have c1 := subR_spec cap (R 1) (R 2) (R 3) (R 4) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (stP R σ w i) (2 ^ i) (by simp [stP, hR])
    (by simp [stP, hR, h3]) (by simp [stP, hR, h4]) (by omega) (by simp [stP, hR]; omega)
  have c2 := WExec.seq c1 (BinW.dupR_spec cap (R 1) (R 3) (R 4) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ (2 ^ i) (by simp [stP, hR]) (by simp [stP, hR, h3]) (by simp [stP, hR, h4]) (by omega))
  have c3 := WExec.seq c2 (wmove_spec cap (R 3) (R 1) (hne (by decide)) (2 ^ i) _ (by simp [stP, hR])
    (by simp [stP, hR]; omega) (by simp [stP, hR]; omega))
  refine WExec.cast cap c3 ?_ ?_
  · apply WState.eq
    · simp [stP]
    · simp [stP]
    · funext j
      have hp : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by rw [pow_succ]; ring
      by_cases j2 : j = R 2
      · subst j2; simp [stP, hR]; omega
      · by_cases j1 : j = R 1
        · subst j1; simp [stP, hR]; omega
        · by_cases j3 : j = R 3
          · subst j3; simp [stP, hR, h3]
          · simp [stP, Function.update_apply, j1, j2, j3]
    · simp [stP]
  · omega

theorem powF_spec (σ : WState ns nr) (w : ℕ) (h0 : σ.val (R 0) = w) (h1 : σ.val (R 1) = 0)
    (h2 : σ.val (R 2) = 0) (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (hcap : 8 * w + 8 ≤ cap) :
    ∃ n, WExec cap (powF R) σ (σ.setv (R 1) (2 ^ Nat.clog 2 (2 * w + 1))) n ∧ n ≤ 1000 * (w + 1) * (w + 2) := by
  have hne : ∀ {i j : Fin 5}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hR : ∀ i j : Fin 5, R i = R j ↔ i = j := fun i j => R.injective.eq_iff
  have c1 := WExec.inc (cap := cap) (R 1) σ (by rw [h1]; omega)
  have c2 := WExec.seq c1 (FsKit.addR_spec cap (R 0) (R 2) (R 3) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ w (by simp [hR, h0]) (by simp [hR, h3]) (by simp [hR, h2]; omega) (by omega))
  have c3 := WExec.seq c2 (FsKit.addR_spec cap (R 0) (R 2) (R 3) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ w (by simp [hR, h0]) (by simp [hR, h3]) (by simp [hR, h2]; omega) (by omega))
  have e0 : ((((σ.setv (R 1) (σ.val (R 1) + 1)).setv (R 2) ((σ.setv (R 1) (σ.val (R 1) + 1)).val (R 2) + w)).setv
      (R 2) (((σ.setv (R 1) (σ.val (R 1) + 1)).setv (R 2) ((σ.setv (R 1) (σ.val (R 1) + 1)).val (R 2) + w)).val
        (R 2) + w))) = stP R σ w 0 := by
    apply WState.eq
    · simp [stP]
    · simp [stP]
    · funext j
      by_cases j2 : j = R 2
      · subst j2; simp [stP, hR, h2]; omega
      · by_cases j1 : j = R 1
        · subst j1; simp [stP, hR, h1]
        · simp [stP, Function.update_apply, j1, j2]
    · simp [stP]
  rw [e0] at c3
  have hm1 : 2 * w + 1 ≤ 2 ^ Nat.clog 2 (2 * w + 1) := Nat.le_pow_clog (by norm_num) _
  have hm2 : 2 ^ Nat.clog 2 (2 * w + 1) ≤ 2 * (2 * w + 1) := pow_clog_le2 _ (by omega)
  have hmle : Nat.clog 2 (2 * w + 1) ≤ 4 * w + 2 := by
    have := Nat.lt_two_pow_self (n := Nat.clog 2 (2 * w + 1)); omega
  have lp := PrimAsm.UnaryPow.flagLoop cap (R 2) (pwBody R) (60 * (2 * w + 2)) (Nat.clog 2 (2 * w + 1))
    (stP R σ w)
    (fun i hi => by
      have := Nat.pow_lt_of_lt_clog hi
      simp [stP, hR]; omega)
    (by simp [stP, hR]; omega)
    (fun i hi => pwBody_spec cap R σ w i h3 h4 (Nat.pow_lt_of_lt_clog hi) hcap)
  refine ⟨_, WExec.cast cap (WExec.seq c3 lp) ?_ le_rfl, ?_⟩
  · apply WState.eq
    · simp [stP]
    · simp [stP]
    · funext j
      by_cases j2 : j = R 2
      · subst j2; simp [stP, hR, h2]; omega
      · simp [stP, Function.update_apply, j2]
    · simp [stP]
  · have hq := Nat.mul_le_mul hmle (le_refl (60 * (2 * w + 2) + 2))
    nlinarith

end Pow

end NearCubicWires.WireExponent3_5.UnionMachine.EwKit
