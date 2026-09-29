import Proof.Wire_3_5.FinalPass.S5TTF

/-! # S5-THR, part 10: unary counts and the input's length (P3:2150-2157)

Register-program pieces for the fixed hash's seed (the hash bits sit at the end of the final pass's input, a framed
suffix of `fpIn`, `PrimAsm.Plan.seedWord`):

* `countU_spec`: a unary stream's ones into a register, its head back to `0` (a second counter);
* `lenM_spec`: the input's length `m = |fpIn|` from the prelude's template `T = sent (m+1)`;
* `walkP_spec`, `copyP_spec`: `k` framed cells skipped, then `k` framed bits copied raw onto a stream.

Paper quantity of the main types: the fixed hash's bits (`filt:soft`, P3:2150-2157), read from the input. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-! ## A unary stream's ones -/

theorem countLoop_spec (P : Fin (ns + 1)) (R R2 : Fin nr) (hRR : R ≠ R2) (k : ℕ) :
    ∀ (j : ℕ) (σ : WState ns nr), σ.st P = List.replicate k true → σ.sh P + j = k →
      σ.val R + j ≤ cap → σ.val R2 + j ≤ cap →
      WExec cap (.whs P (.seq (.fwd P) (.seq (.inc R) (.inc R2)))) σ
        (((σ.seth P k).setv R (σ.val R + j)).setv R2 (σ.val R2 + j)) (11 * j + 1)
  | 0, σ, hs, hp, _, _ => by
    have hb : wbit σ P = false := by
      unfold wbit; rw [hs, show σ.sh P = k by omega]; exact UnionMachine.FrontFill.read_true_ge k k le_rfl
    have e : ((σ.seth P k).setv R (σ.val R + 0)).setv R2 (σ.val R2 + 0) = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = P
        · subst hi; simp; omega
        · simp [Function.update_apply, hi]
      · rfl
      · funext r
        simp only [WState.setv_val, WState.seth_val, Function.update_apply]
        by_cases a1 : r = R2 <;> by_cases a2 : r = R <;> simp_all
      · rfl
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | j + 1, σ, hs, hp, hc1, hc2 => by
    have hb : wbit σ P = true := by
      unfold wbit; rw [hs]; exact UnionMachine.FrontFill.read_true k _ (by omega)
    have e1 := WExec.fwd (cap := cap) P σ
    have v1 : (σ.seth P (σ.sh P + 1)).val R = σ.val R := rfl
    have v2 : ((σ.seth P (σ.sh P + 1)).setv R (σ.val R + 1)).val R2 = σ.val R2 := by
      rw [wsetv_val_ne _ _ (Ne.symm hRR)]; rfl
    have e2 := WExec.inc (cap := cap) R (σ.seth P (σ.sh P + 1)) (by rw [v1]; omega)
    rw [v1] at e2
    have e3 := WExec.inc (cap := cap) R2 ((σ.seth P (σ.sh P + 1)).setv R (σ.val R + 1)) (by rw [v2]; omega)
    rw [v2] at e3
    have ih := countLoop_spec P R R2 hRR k j
      (((σ.seth P (σ.sh P + 1)).setv R (σ.val R + 1)).setv R2 (σ.val R2 + 1))
      (by simpa using hs) (by simp; omega)
      (by rw [wsetv_val_ne _ _ hRR, wsetv_val_self]; omega) (by rw [wsetv_val_self]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = P
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · rfl
    · funext r
      simp only [WState.setv_val, WState.seth_val, Function.update_apply]
      by_cases a1 : r = R2 <;> by_cases a2 : r = R <;> simp_all <;> omega
    · rfl

/-- **A unary stream's ones** into `R` (`R2` a scratch counter), the head back at `0`. -/
def countU (P : Fin (ns + 1)) (R R2 : Fin nr) : WM ns nr :=
  .seq (.whs P (.seq (.fwd P) (.seq (.inc R) (.inc R2)))) (WM.rewind P R2)

theorem countU_spec (P : Fin (ns + 1)) (R R2 : Fin nr) (hRR : R ≠ R2) (k : ℕ) (σ : WState ns nr)
    (hs : σ.st P = List.replicate k true) (hp : σ.sh P = 0) (hR : σ.val R = 0) (hR2 : σ.val R2 = 0)
    (hk : k ≤ cap) :
    WExec cap (countU P R R2) σ (σ.setv R k) (16 * k + 3) := by
  have e1 := countLoop_spec cap P R R2 hRR k k σ hs (by omega) (by omega) (by omega)
  rw [hR, hR2, Nat.zero_add] at e1
  have e2 := wrewind_spec cap P R2 k (((σ.seth P k).setv R k).setv R2 k) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = P
    · subst hi; simp [hp]
    · simp [Function.update_apply, hi]
  · rfl
  · funext r
    simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases a1 : r = R2 <;> by_cases a2 : r = R <;> simp_all
  · rfl

/-! ## The input's length -/

/-- `M := m` from the template `sent (m+1)`, its head back at `0`. -/
def lenM (T : Fin (ns + 1)) (M : Fin nr) : WM ns nr :=
  .seq (.fwd T) (.seq (.whs T (.seq (.fwd T) (.inc M))) (.seq (rewSent T) (.dec M)))

theorem lenLoopT_spec (T : Fin (ns + 1)) (M : Fin nr) (c : ℕ) : ∀ (j : ℕ) (σ : WState ns nr),
    σ.st T = sent c → σ.sh T + j = c + 1 → 1 ≤ σ.sh T → σ.val M + j ≤ cap →
    WExec cap (.whs T (.seq (.fwd T) (.inc M))) σ ((σ.seth T (c + 1)).setv M (σ.val M + j)) (7 * j + 1)
  | 0, σ, hs, hp, _, _ => by
    have hb : wbit σ T = false := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e : (σ.seth T (c + 1)).setv M (σ.val M + 0) = σ := by
      apply WState.eq
      · funext i; by_cases hi : i = T
        · subst hi; simp; omega
        · simp [Function.update_apply, hi]
      · rfl
      · funext r; by_cases a : r = M
        · subst a; simp
        · simp [Function.update_apply, a]
      · rfl
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | j + 1, σ, hs, hp, h1, hc => by
    have hb : wbit σ T = true := by unfold wbit; rw [hs, read_sent]; simp; omega
    have e1 := WExec.fwd (cap := cap) T σ
    have v1 : (σ.seth T (σ.sh T + 1)).val M = σ.val M := rfl
    have e2 := WExec.inc (cap := cap) M (σ.seth T (σ.sh T + 1)) (by rw [v1]; omega)
    rw [v1] at e2
    have ih := lenLoopT_spec T M c j ((σ.seth T (σ.sh T + 1)).setv M (σ.val M + 1))
      (by simpa using hs) (by simp; omega) (by simp) (by rw [wsetv_val_self]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = T
      · subst hi; simp
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases a : r = M
      · subst a; simp; omega
      · simp [Function.update_apply, a]
    · rfl

theorem lenM_spec (T : Fin (ns + 1)) (M : Fin nr) (m : ℕ) (σ : WState ns nr) (hs : σ.st T = sent (m + 1))
    (hp : σ.sh T = 0) (hM : σ.val M = 0) (hc : m + 1 ≤ cap) :
    WExec cap (lenM T M) σ (σ.setv M m) (10 * m + 20) := by
  have e1 := WExec.fwd (cap := cap) T σ
  rw [hp] at e1
  have v1 : (σ.seth T (0 + 1)).val M = 0 := hM
  have e2 := lenLoopT_spec cap T M (m + 1) (m + 1) (σ.seth T (0 + 1)) (by simpa using hs) (by simp; omega) (by simp)
    (by rw [v1]; omega)
  rw [wseth_seth, v1] at e2
  simp only [Nat.zero_add] at e2
  have e3 := rewSent_spec cap T (m + 1) ((σ.seth T (m + 1 + 1)).setv M (m + 1))
    (by simpa using hs) (by simp)
  have v2 : (((σ.seth T (m + 1 + 1)).setv M (m + 1)).seth T 0).val M = m + 1 := by simp
  have e4 := WExec.dec (cap := cap) M (((σ.seth T (m + 1 + 1)).setv M (m + 1)).seth T 0) (by rw [v2]; omega)
  rw [v2, Nat.add_sub_cancel] at e4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = T
    · subst hi; simp [hp]
    · simp [Function.update_apply, hi]
  · rfl
  · funext r; by_cases a : r = M
    · subst a; simp [hM]
    · simp [Function.update_apply, a]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
