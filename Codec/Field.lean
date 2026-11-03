import Codec.Emit
import Worker.Format
import Proof.PCP.VerifierDecodingLookup

/-!
# The worker's field readers (W3): unary counts and stripped numbers

The guess is stored on a RAW stream `W` (`false` past its end), in the format of `Worker.Format`. This file gives
* the pure facts: a unary count read at any position (`readCount_drop`), trailing zeros `tz`, and the J3 word of the
  little-endian value of a bit list (`natWord_value`: `1^L 0` then the bits up to the last `1`);
* `countW`: the machine reading a unary count into a register, specified on every stream.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicGates.Close.Worker.Format

/-! ## Pure facts -/

theorem headD_drop (w : List Bool) (p : ℕ) : (w.drop p).headD false = w.getD p false := by
  rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

theorem drop_succ_tail (w : List Bool) (p : ℕ) : w.drop (p + 1) = (w.drop p).tail := by
  rw [List.tail_drop]


/-! ## Reading a unary count -/

variable {ns nr : ℕ} (cap : ℕ)

/-- Read a unary count `1^k 0` on the raw stream `W` into register `K` (added to it). -/
def countW (W : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .seq (.whs W (.seq (.fwd W) (.inc K))) (.fwd W)

theorem wbit_eq (σ : WState ns nr) (i : Fin (ns + 1)) : wbit σ i = ((σ.st i).drop (σ.sh i)).headD false := by
  rw [headD_drop]; rfl

theorem countLoop_spec (W : Fin (ns + 1)) (K : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), (readCount ((σ.st W).drop (σ.sh W))).1 = k → σ.val K + k ≤ cap →
      WExec cap (.whs W (.seq (.fwd W) (.inc K))) σ ((σ.seth W (σ.sh W + k)).setv K (σ.val K + k)) (7 * k + 1)
  | 0, σ, hk, _ => by
    have hb : wbit σ W = false := by
      rw [wbit_eq]
      rcases hw : (σ.st W).drop (σ.sh W) with _ | ⟨b, r⟩
      · rfl
      · cases b
        · rfl
        · rw [hw] at hk; simp [readCount] at hk
    refine WExec.cast cap (WExec.whsF hb) ?_ (by omega)
    apply WState.eq <;> simp
  | k + 1, σ, hk, hcap => by
    rcases hw : (σ.st W).drop (σ.sh W) with _ | ⟨b, r⟩
    · rw [hw] at hk; simp [readCount] at hk
    · cases b
      · rw [hw] at hk; simp [readCount] at hk
      · have hb : wbit σ W = true := by rw [wbit_eq, hw]; rfl
        rw [hw] at hk
        simp only [readCount, Nat.add_right_cancel_iff] at hk
        have h1 : WExec cap (.seq (.fwd W) (.inc K)) σ ((σ.seth W (σ.sh W + 1)).setv K (σ.val K + 1)) 5 :=
          WExec.seq (WExec.fwd W σ) (WExec.inc K _ (by simp; omega))
        set σ1 := (σ.seth W (σ.sh W + 1)).setv K (σ.val K + 1) with hσ1
        have hr : (σ1.st W).drop (σ1.sh W) = r := by
          simp [hσ1, drop_succ_tail, hw]
        have h2 := countLoop_spec W K k σ1 (by rw [hr]; exact hk) (by simp [hσ1]; omega)
        refine WExec.cast cap (WExec.whsT hb h1 h2) ?_ (by omega)
        apply WState.eq
        · funext j; by_cases hj : j = W
          · subst hj; simp [hσ1]; omega
          · simp [hσ1, Function.update_of_ne hj]
        · simp [hσ1]
        · funext j; by_cases hj : j = K
          · subst hj; simp [hσ1]; omega
          · simp [hσ1, Function.update_of_ne hj]
        · simp [hσ1]

/-- **The count reader**, on every stream: `K` gains the count, the head moves past it (and its closing `0`). -/
theorem countW_spec (W : Fin (ns + 1)) (K : Fin nr) (σ : WState ns nr)
    (hcap : σ.val K + (readCount ((σ.st W).drop (σ.sh W))).1 ≤ cap) :
    WExec cap (countW W K) σ
      ((σ.seth W (σ.sh W + (readCount ((σ.st W).drop (σ.sh W))).1 + 1)).setv K
        (σ.val K + (readCount ((σ.st W).drop (σ.sh W))).1))
      (7 * (readCount ((σ.st W).drop (σ.sh W))).1 + 3) := by
  set k := (readCount ((σ.st W).drop (σ.sh W))).1 with hk
  have h1 := countLoop_spec cap W K k σ hk.symm hcap
  have h2 := WExec.fwd (cap := cap) W ((σ.seth W (σ.sh W + k)).setv K (σ.val K + k))
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = W
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · simp
  · simp
  · simp

end NearCubicGates.Close.Codec
