import Proof.Wire_3_5.UnionMachine.BinW

/-! # C6, the FILTER setup, part 1: register arithmetic and unary words, exact final states

The FILTER setup (`FiltSetup.FiltSetupSpec2`, the type) computes the regular filter's numbers in registers
and writes unary rulers; every piece here states its EXACT final state as one update of its entry state, the scratch
back at `0`:
* **`addR_spec`** (`Y += X`, `X` kept, program `BinW.dupR`), **`incK_spec`** (`r += c`), **`mulK_spec`**
  (`Y += c·X`), **`mulR_spec`** (`Y += X·Z`, `X`, `Z` kept);
* **`unaryW_spec`**: `1^v` on a blank stream (head back at `0`) from a register `v` (kept).

Paper quantity: none (register programs for the setup of `filt:gap`'s regular filter, P3:2019-2054). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR dupL_spec bsetv_self)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Adding a register -/

/-- **`Y += X`** (`X` kept, the scratch `T` at `0`), by `BinW.dupR`. -/
theorem addR_spec (X Y T : Fin nr) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) (σ : WState ns nr) (x : ℕ)
    (hx : σ.val X = x) (ht : σ.val T = 0) (hc : σ.val Y + x ≤ cap) (hcx : x ≤ cap) :
    WExec cap (dupR X Y T) σ (σ.setv Y (σ.val Y + x)) (18 * x + 3) := by
  have h1 := dupL_spec cap X Y T hXY hXT hYT x σ hx (by omega) hc (by omega)
  rw [ht, Nat.zero_add] at h1
  have h2 := wmove_spec cap T X (Ne.symm hXT) x (((σ.setv X 0).setv Y (σ.val Y + x)).setv T x) (by simp)
    (by simp <;> omega) (by simp [hXT, hXY] <;> omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext j
    simp only [WState.setv_val, Function.update_apply]
    by_cases hjX : j = X
    · subst hjX; simp [hXY, hXT, hx]
    · by_cases hjY : j = Y
      · subst hjY; simp [hjX, hYT]
      · by_cases hjT : j = T
        · subst hjT; simp [hjX, hjY, ht]
        · simp [hjX, hjY, hjT]
  · rfl

/-! ## Adding a constant -/

/-- `r += c`. -/
def incK (r : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | c + 1 => .seq (.inc r) (incK r c)

theorem incK_spec (r : Fin nr) : ∀ (c : ℕ) (σ : WState ns nr), σ.val r + c ≤ cap →
    WExec cap (incK r c) σ (σ.setv r (σ.val r + c)) (4 * c)
  | 0, σ, _ => by
    rw [Nat.add_zero, wsetv_same]
    exact WExec.skip σ
  | c + 1, σ, hc => by
    have h1 := WExec.inc (cap := cap) r σ (by omega)
    have h2 := incK_spec r c (σ.setv r (σ.val r + 1)) (by simp; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
    rw [wsetv_setv]
    congr 1
    simp; omega

/-! ## Adding a multiple -/

/-- `Y += c·X`. -/
def mulK (X Y T : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | c + 1 => .seq (dupR X Y T) (mulK X Y T c)

theorem mulK_spec (X Y T : Fin nr) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) (x : ℕ) :
    ∀ (c : ℕ) (σ : WState ns nr), σ.val X = x → σ.val T = 0 → σ.val Y + c * x ≤ cap → x ≤ cap →
      WExec cap (mulK X Y T c) σ (σ.setv Y (σ.val Y + c * x)) (c * (18 * x + 4))
  | 0, σ, _, _, _, _ => by
    rw [Nat.zero_mul, Nat.add_zero, wsetv_same]
    exact WExec.mono (WExec.skip σ) (Nat.zero_le _)
  | c + 1, σ, hx, ht, hc, hcx => by
    have h1 := addR_spec cap X Y T hXY hXT hYT σ x hx ht (by rw [Nat.succ_mul] at hc; omega) hcx
    have h2 := mulK_spec X Y T hXY hXT hYT x c (σ.setv Y (σ.val Y + x)) (by simp [hXY, hx])
      (by simp [Ne.symm hYT, ht]) (by simp; rw [Nat.succ_mul] at hc; omega) hcx
    refine WExec.cast cap (WExec.seq h1 h2) ?_ ?_
    · rw [wsetv_setv]
      congr 1
      simp [Nat.succ_mul]; omega
    · have e : (c + 1) * (18 * x + 4) = c * (18 * x + 4) + (18 * x + 4) := by ring
      rw [e]; omega

/-! ## Adding a product -/

/-- The product loop: `Y += U·X`, `U := 0`. -/
def mulL (X Y T U : Fin nr) : WM ns nr := .whr U (.seq (.dec U) (dupR X Y T))

theorem mulL_spec (X Y T U : Fin nr) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) (hUX : U ≠ X) (hUY : U ≠ Y)
    (hUT : U ≠ T) (x : ℕ) :
    ∀ (u : ℕ) (σ : WState ns nr), σ.val U = u → σ.val X = x → σ.val T = 0 → σ.val Y + u * x ≤ cap → x ≤ cap →
      u ≤ cap → WExec cap (mulL X Y T U) σ ((σ.setv U 0).setv Y (σ.val Y + u * x)) (u * (18 * x + 7) + 1)
  | 0, σ, hu, _, _, _, _, _ => by
    rw [Nat.zero_mul, Nat.add_zero, bsetv_self σ U 0 hu, wsetv_same]
    exact WExec.mono (WExec.whrF hu) (by omega)
  | u + 1, σ, hu, hx, ht, hc, hcx, hcu => by
    have h1 := WExec.dec (cap := cap) U σ (by omega)
    have h2 := addR_spec cap X Y T hXY hXT hYT (σ.setv U (σ.val U - 1)) x (by simp [Ne.symm hUX, hx])
      (by simp [Ne.symm hUT, ht]) (by simp [Ne.symm hUY]; rw [Nat.succ_mul] at hc; omega) hcx
    have h3 := mulL_spec X Y T U hXY hXT hYT hUX hUY hUT x u
      ((σ.setv U (σ.val U - 1)).setv Y ((σ.setv U (σ.val U - 1)).val Y + x))
      (by simp [hUY]; omega) (by simp [hXY, Ne.symm hUX, hx]) (by simp [Ne.symm hYT, Ne.symm hUT, ht])
      (by simp [Ne.symm hUY]; rw [Nat.succ_mul] at hc; omega) hcx (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) h3) ?_ ?_
    · apply WState.eq
      · rfl
      · rfl
      · funext j
        simp only [WState.setv_val, Function.update_apply]
        by_cases hjY : j = Y
        · subst hjY; simp [Ne.symm hUY, Nat.succ_mul]; omega
        · by_cases hjU : j = U
          · subst hjU; simp [hjY]
          · simp [hjY, hjU]
      · rfl
    · have e : (u + 1) * (18 * x + 7) = u * (18 * x + 7) + (18 * x + 7) := by ring
      rw [e]; omega

/-- **`Y += X·Z`** (`X`, `Z` kept; the scratch `T`, `U` at `0`). -/
def mulR (X Z Y T U : Fin nr) : WM ns nr := .seq (dupR Z U T) (mulL X Y T U)

theorem mulR_spec (X Z Y T U : Fin nr) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) (hUX : U ≠ X) (hUY : U ≠ Y)
    (hUT : U ≠ T) (hZU : Z ≠ U) (hZT : Z ≠ T) (hZY : Z ≠ Y) (σ : WState ns nr) (x z : ℕ) (hx : σ.val X = x)
    (hz : σ.val Z = z) (ht : σ.val T = 0) (hu : σ.val U = 0) (hc : σ.val Y + z * x ≤ cap) (hcx : x ≤ cap)
    (hcz : z ≤ cap) :
    WExec cap (mulR X Z Y T U) σ (σ.setv Y (σ.val Y + z * x)) (18 * z + 3 + 1 + (z * (18 * x + 7) + 1)) := by
  have h1 := BinW.dupR_spec cap Z U T hZU hZT hUT σ z hz hu ht hcz
  have h2 := mulL_spec cap X Y T U hXY hXT hYT hUX hUY hUT x z (σ.setv U z) (by simp) (by simp [Ne.symm hUX, hx])
    (by simp [Ne.symm hUT, ht]) (by simp [Ne.symm hUY]; omega) hcx hcz
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j
    simp only [WState.setv_val, Function.update_apply]
    by_cases hjY : j = Y
    · subst hjY; simp [Ne.symm hUY]
    · by_cases hjU : j = U
      · subst hjU; simp [hjY, hu]
      · simp [hjY, hjU]
  · rfl

/-! ## Unary words -/

/-- **`1^v` on the blank `O`** (head back at `0`) from the register `V` (kept); scratch `A`, `T`, `P`. -/
def unaryW (O : Fin (ns + 1)) (V A T P : Fin nr) : WM ns nr :=
  .seq (dupR V A T) (.seq (.whr A (.seq (.dec A) (emitC O P true))) (WM.rewind O P))

/-- The state after `i` ones. -/
def stU (σ : WState ns nr) (O : Fin (ns + 1)) (A P : Fin nr) (v i : ℕ) : WState ns nr :=
  (((σ.sets O (List.replicate i true)).seth O i).setv A (v - i)).setv P i

theorem unaryL_spec (O : Fin (ns + 1)) (A P : Fin nr) (hAP : A ≠ P) (σ : WState ns nr) (v : ℕ) (hcap : v + 1 ≤ cap) :
    ∀ j i : ℕ, i + j = v →
      WExec cap (.whr A (.seq (.dec A) (emitC O P true))) (stU σ O A P v i) (stU σ O A P v v) (j * 11 + 1)
  | 0, i, h => by
    have hi : i = v := by omega
    subst hi
    exact WExec.whrF (by simp [stU, hAP])
  | j + 1, i, h => by
    have h1 := WExec.dec (cap := cap) A (stU σ O A P v i) (by simp [stU, hAP]; omega)
    have hO : ((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)).sh O =
        (((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)).st O).length := by simp [stU]
    have h2 := emitC_spec cap O P true ((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)) hO
      (by simp [stU, Ne.symm hAP]; omega)
    have ih := unaryL_spec O A P hAP σ v hcap j (i + 1) (by omega)
    have e : (((((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)).sets O
        (((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)).st O ++ [true])).seth O
        (((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)).sh O + 1)).setv P
        (((stU σ O A P v i).setv A ((stU σ O A P v i).val A - 1)).val P + 1)) = stU σ O A P v (i + 1) := by
      apply WState.eq
      · funext k
        by_cases hk : k = O
        · subst hk; simp [stU]
        · simp [stU, hk]
      · funext k
        by_cases hk : k = O
        · subst hk; simp [stU, ← List.replicate_succ']
        · simp [stU, hk]
      · funext k
        simp only [stU, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
        by_cases hkP : k = P
        · subst hkP; simp [Ne.symm hAP]
        · by_cases hkA : k = A
          · subst hkA; simp [hkP]; omega
          · simp [hkP, hkA]
      · rfl
    rw [e] at h2
    refine WExec.mono (WExec.whrT (by simp [stU, hAP]; omega) (WExec.seq h1 h2) ih) ?_
    have e2 : (j + 1) * 11 = j * 11 + 11 := by ring
    rw [e2]; omega

theorem unaryW_spec (O : Fin (ns + 1)) (V A T P : Fin nr) (hVA : V ≠ A) (hVT : V ≠ T) (hAT : A ≠ T) (hAP : A ≠ P)
    (hVP : V ≠ P) (hTP : T ≠ P) (σ : WState ns nr) (v : ℕ) (hv : σ.val V = v) (ha : σ.val A = 0) (ht : σ.val T = 0)
    (hp : σ.val P = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hcap : v + 1 ≤ cap) :
    WExec cap (unaryW O V A T P) σ (σ.sets O (List.replicate v true)) (18 * v + 3 + 1 + (v * 11 + 1 + 1 + (5 * v + 1))) := by
  have d := BinW.dupR_spec cap V A T hVA hVT hAT σ v hv ha ht (by omega)
  have e0 : σ.setv A v = stU σ O A P v 0 := by
    apply WState.eq
    · funext k
      by_cases hk : k = O
      · subst hk; simp [stU, hOh]
      · simp [stU, hk]
    · funext k
      by_cases hk : k = O
      · subst hk; simp [stU, hO]
      · simp [stU, hk]
    · funext k
      simp only [stU, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      by_cases hkP : k = P
      · subst hkP; simp [Ne.symm hAP, hp]
      · simp [hkP]
    · rfl
  rw [e0] at d
  have lp := unaryL_spec cap O A P hAP σ v hcap v 0 (by omega)
  have rw7 := wrewind_spec cap O P v (stU σ O A P v v) (by simp [stU]) (by simp [stU]; omega)
  refine WExec.cast cap (WExec.seq d (WExec.seq lp rw7)) ?_ le_rfl
  apply WState.eq
  · funext k
    by_cases hk : k = O
    · subst hk; simp [stU, hOh]
    · simp [stU, hk]
  · funext k
    by_cases hk : k = O
    · subst hk; simp [stU]
    · simp [stU, hk]
  · funext k
    simp only [stU, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
    by_cases hkP : k = P
    · subst hkP; simp [hp]
    · by_cases hkA : k = A
      · subst hkA; simp [hkP, ha]
      · simp [hkP, hkA]
  · rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FsKit
