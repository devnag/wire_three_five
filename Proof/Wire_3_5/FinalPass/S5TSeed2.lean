import Proof.Wire_3_5.FinalPass.S5TSeed1

/-! # S5-THR, part 11: the fixed hash's bits copied from the input (P3:2150-2157)

The final pass's input `fpIn` ends with `frame (List.ofFn s)`, the fixed hash's bits (`PrimAsm.Plan.seedWord`). On
the input stream (`frame fpIn`, one framed cell pair per bit) the program skips the first `|fpIn| − c` bits and copies
the last `c = |frame (ofFn s)|` bits raw onto a blank stream, then returns both heads to `0`:

* `walkP_spec` (`2k` cells forward), `copyRaw_spec` (`k` framed bits copied raw);
* `copySuffix_spec`: the suffix of length `c` of the framed word on `I` copied onto `O`, every head back at `0`.

Paper quantity of the main type: the fixed hash's bits (`filt:soft`, P3:2150-2157), read from the input. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-- `2k` cells forward on `I`, `k` from `K`. -/
def walkP (I : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (.seq (.fwd I) (.fwd I)))

theorem walkP_spec (I : Fin (ns + 1)) (K : Fin nr) : ∀ (k : ℕ) (σ : WState ns nr), σ.val K = k → k ≤ cap →
    WExec cap (walkP I K) σ ((σ.setv K 0).seth I (σ.sh I + 2 * k)) (7 * k + 1)
  | 0, σ, h0, _ => by
    have e : (σ.setv K 0).seth I (σ.sh I + 2 * 0) = σ := by
      rw [Nat.mul_zero, Nat.add_zero, show (0 : ℕ) = σ.val K from h0.symm, wsetv_same]
      rw [show σ.sh I = σ.sh I from rfl, HashSeed.seth_same]
    rw [e]; exact WExec.whrF h0
  | k + 1, σ, h0, hc => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    rw [h0, Nat.add_sub_cancel] at e1
    have e2 := WExec.fwd (cap := cap) I (σ.setv K k)
    have e3 := WExec.fwd (cap := cap) I ((σ.setv K k).seth I ((σ.setv K k).sh I + 1))
    have ih := walkP_spec I K k (((σ.setv K k).seth I ((σ.setv K k).sh I + 1)).seth I
      (((σ.setv K k).seth I ((σ.setv K k).sh I + 1)).sh I + 1)) (by simp) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = I
      · subst hi; simp; omega
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases a : r = K
      · subst a; simp
      · simp [Function.update_apply, a]
    · rfl

/-- `k` framed bits of `I` copied raw onto `O`, `k` from `K`. -/
def copyRaw (I O : Fin (ns + 1)) (K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.fwd I) (.seq (.ifs I (emit1 O true) (emit1 O false)) (.fwd I))))

theorem copyRaw_spec (I O : Fin (ns + 1)) (hIO : I ≠ O) (K : Fin nr) (w : List Bool) :
    ∀ (k p : ℕ) (σ : WState ns nr), σ.st I = frame w → σ.sh I = 2 * p → p + k ≤ w.length →
      σ.val K = k → k ≤ cap → σ.sh O = (σ.st O).length →
      WExec cap (copyRaw I O K) σ ((appW (σ.setv K 0) O ((w.drop p).take k)).seth I (2 * (p + k))) (12 * k + 1)
  | 0, p, σ, hs, hp, _, h0, _, hO => by
    have e : (appW (σ.setv K 0) O ((w.drop p).take 0)).seth I (2 * (p + 0)) = σ := by
      rw [List.take_zero, appW_nil _ O (by simpa using hO)]
      apply WState.eq
      · funext i; by_cases hi : i = I
        · subst hi; simp; omega
        · simp [Function.update_apply, hi]
      · rfl
      · funext r; by_cases a : r = K
        · subst a; simp; omega
        · simp [Function.update_apply, a]
      · rfl
    rw [e]; exact WExec.mono (WExec.whrF h0) (by omega)
  | k + 1, p, σ, hs, hp, hpk, h0, hc, hO => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    rw [h0, Nat.add_sub_cancel] at e1
    have e2 := WExec.fwd (cap := cap) I (σ.setv K k)
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = (σ.setv K k).seth I ((σ.setv K k).sh I + 1) := ⟨_, rfl⟩
    rw [← hσ2] at e2
    have hb : wbit σ2 I = w.getD p false := by
      unfold wbit; rw [hσ2]; simp only [WState.seth_st, WState.setv_st, WState.seth_sh, Function.update_self,
        WState.setv_sh, hs, hp]
      exact read_frame_odd w p (by omega)
    have hO2 : σ2.sh O = (σ2.st O).length := by rw [hσ2]; simp [Function.update_apply, Ne.symm hIO, hO]
    have e3 : WExec cap (.ifs I (emit1 O true) (emit1 O false)) σ2 (appW σ2 O [w.getD p false]) 4 := by
      cases hwp : w.getD p false
      · rw [hwp] at hb; exact WExec.ifsF hb (emit1_spec cap O false σ2 hO2)
      · rw [hwp] at hb; exact WExec.ifsT hb (emit1_spec cap O true σ2 hO2)
    have e4 := WExec.fwd (cap := cap) I (appW σ2 O [w.getD p false])
    have ih := copyRaw_spec I O hIO K w k (p + 1) ((appW σ2 O [w.getD p false]).seth I
      ((appW σ2 O [w.getD p false]).sh I + 1))
      (by rw [hσ2]; simp [Function.update_apply, hIO, hs]) (by rw [hσ2]; simp [Function.update_apply, hIO, hp]; omega)
      (by omega) (by rw [hσ2]; simp) (by omega) (by simp [Function.update_apply, Ne.symm hIO])
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ih) ?_ (by omega)
    have htake : (w.drop p).take (k + 1) = w.getD p false :: (w.drop (p + 1)).take k := by
      rw [List.drop_eq_getElem_cons (by omega), List.take_succ_cons, List.getD_eq_getElem _ _ (by omega)]
    rw [hσ2, htake]
    apply WState.eq
    · funext i; by_cases hi : i = I
      · subst hi; simp [Function.update_apply, hIO]; omega
      · by_cases hiO : i = O
        · subst hiO; simp [Function.update_apply, hi]; omega
        · simp [Function.update_apply, hi, hiO]
    · funext i; by_cases hiO : i = O
      · subst hiO; simp [Function.update_apply]
      · simp [Function.update_apply, hiO]
    · funext r; by_cases a : r = K
      · subst a; simp
      · simp [Function.update_apply, a]
    · rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
