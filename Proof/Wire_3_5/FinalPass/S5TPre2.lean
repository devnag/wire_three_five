import Proof.Wire_3_5.FinalPass.S5TPre1

/-! # S5-THR, part 2: the front's junk-free count `(|fpIn|+1)^{D+1}` (P3:3170-3181)

A register-free word program (`preW`) that reads the framed input `frame u` on stream `I` and leaves, every head back
at `0` and nothing else touched:
* the template `T = sent (|u|+1)` (`lenT`: one `1` per framed bit, the heads returned in lockstep with the sentinel);
* the powers `xs j = sent ((|u|+1)^{j+1})`, `j ≤ D` (`sentCopy`, then `D` products `mulW`);
* the count `C = 1^{(|u|+1)^{D+1}}` (`plainCopy`), the fill count of the front's register tapes.

Main declarations: `lenT_spec`, `sentCopy_spec`, `plainCopy_spec`, `chainSt`, **`chainW_spec`**, `preSt`,
**`preW_spec`**. Paper quantity: the front's register capacity (its unary count). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The template from the input -/

/-- One `1` on `T` per framed bit of `I`. -/
def lenLoop (I T : Fin (ns + 1)) : WM ns nr := .whs I (.seq (.fwd I) (.seq (.fwd I) (emit1 T true)))

theorem lenLoop_spec (I T : Fin (ns + 1)) (hIT : I ≠ T) (u : List Bool) : ∀ (k : ℕ) (σ : WState ns nr),
    σ.st I = frame u → σ.sh I + 2 * k = 2 * u.length → σ.sh T = (σ.st T).length →
    WExec cap (lenLoop I T) σ ((appW σ T (List.replicate k true)).seth I (2 * u.length)) (9 * k + 1)
  | 0, σ, hs, hp, hT => by
    have hb : wbit σ I = false := by
      unfold wbit; rw [hs, show σ.sh I = 2 * u.length by omega, read_frame_even]; simp
    have e : (appW σ T (List.replicate 0 true)).seth I (2 * u.length) = σ := by
      rw [List.replicate_zero, appW_nil σ T hT, show 2 * u.length = σ.sh I by omega, HashSeed.seth_same]
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | k + 1, σ, hs, hp, hT => by
    have hb : wbit σ I = true := by
      unfold wbit; rw [hs, show σ.sh I = 2 * (u.length - (k + 1)) by omega, read_frame_even]; simp; omega
    have e1 := WExec.fwd (cap := cap) I σ
    have e2 := WExec.fwd (cap := cap) I (σ.seth I (σ.sh I + 1))
    rw [wseth_seth, show (σ.seth I (σ.sh I + 1)).sh I + 1 = σ.sh I + 2 by simp] at e2
    have e3 := emit1_spec cap T true (σ.seth I (σ.sh I + 2)) (by simp [Function.update_apply, Ne.symm hIT, hT])
    have ih := lenLoop_spec I T hIT u k (appW (σ.seth I (σ.sh I + 2)) T [true])
      (by simp [Function.update_apply, hIT, hs]) (by simp [Function.update_apply, hIT]; omega)
      (by simp [Function.update_apply, Ne.symm hIT])
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    rw [appW_appW, appW_seth _ (Ne.symm hIT), wseth_seth, List.replicate_succ]
    rfl

/-- Back to the sentinel of `T`, stream `I` two cells per step. -/
def rewLock2 (T I : Fin (ns + 1)) : WM ns nr := .whs T (.seq (.bwd T) (.seq (.bwd I) (.bwd I)))

theorem rewLock2_spec (T I : Fin (ns + 1)) (hTI : T ≠ I) (c : ℕ) : ∀ (p : ℕ) (σ : WState ns nr),
    σ.st T = sent c → σ.sh T = p → p ≤ c → σ.sh I ≤ 2 * p →
    WExec cap (rewLock2 T I) σ ((σ.seth T 0).seth I 0) (7 * p + 1)
  | 0, σ, hs, hp, _, hI => by
    have hb : wbit σ T = false := by unfold wbit; rw [hs, hp, read_sent]; simp
    have e : (σ.seth T 0).seth I 0 = σ := by
      apply WState.eq
      · funext j
        by_cases hjI : j = I
        · subst hjI; simp; omega
        · by_cases hjT : j = T
          · subst hjT; simp [Function.update_apply, hjI, hp]
          · simp [Function.update_apply, hjI, hjT]
      · rfl
      · rfl
      · rfl
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | p + 1, σ, hs, hp, hc, hI => by
    have hb : wbit σ T = true := by unfold wbit; rw [hs, hp, read_sent]; simp; omega
    have e1 := WExec.bwd (cap := cap) T σ
    have e2 := WExec.bwd (cap := cap) I (σ.seth T (σ.sh T - 1))
    have e3 := WExec.bwd (cap := cap) I ((σ.seth T (σ.sh T - 1)).seth I ((σ.seth T (σ.sh T - 1)).sh I - 1))
    have ih := rewLock2_spec T I hTI c p (((σ.seth T (σ.sh T - 1)).seth I ((σ.seth T (σ.sh T - 1)).sh I - 1)).seth I
      (((σ.seth T (σ.sh T - 1)).seth I ((σ.seth T (σ.sh T - 1)).sh I - 1)).sh I - 1))
      (by simpa using hs) (by simp [Function.update_apply, hTI]; omega) (by omega)
      (by simp [Function.update_apply, Ne.symm hTI]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hjI : j = I
      · subst hjI; simp
      · by_cases hjT : j = T
        · subst hjT; simp [Function.update_apply, hjI]
        · simp [Function.update_apply, hjI, hjT]
    · rfl
    · rfl
    · rfl

/-- **The template**: `T := sent (|u|+1)` from `frame u` on `I`, every head back at `0`. -/
def lenT (I T : Fin (ns + 1)) : WM ns nr :=
  .seq (emit1 T false) (.seq (emit1 T true) (.seq (lenLoop I T) (.seq (.bwd T) (rewLock2 T I))))

theorem lenT_spec (I T : Fin (ns + 1)) (hIT : I ≠ T) (u : List Bool) (σ : WState ns nr) (hI : σ.st I = frame u)
    (hIh : σ.sh I = 0) (hT : σ.st T = []) (hTh : σ.sh T = 0) :
    WExec cap (lenT I T) σ (σ.sets T (sent (u.length + 1))) (16 * u.length + 20) := by
  have e1 := emit1_spec cap T false σ (by rw [hT, hTh]; rfl)
  have e2 := emit1_spec cap T true (appW σ T [false]) (by simp)
  rw [appW_appW] at e2
  have e3 := lenLoop_spec cap I T hIT u u.length (appW σ T ([false] ++ [true]))
    (by simp [Function.update_apply, hIT, hI]) (by simp [Function.update_apply, hIT, hIh]) (by simp)
  rw [appW_appW] at e3
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (appW σ T ([false] ++ [true] ++ List.replicate u.length true)).seth I
      (2 * u.length) := ⟨_, rfl⟩
  rw [← hτ] at e3
  have hτT : τ.st T = sent (u.length + 1) := by
    rw [hτ]; simp [hT, sent, List.replicate_succ]
  have e4 := WExec.bwd (cap := cap) T τ
  have e5 := rewLock2_spec cap T I (Ne.symm hIT) (u.length + 1) (u.length + 1) (τ.seth T (τ.sh T - 1))
    (by simpa using hτT) (by rw [hτ]; simp [Function.update_apply, Ne.symm hIT, hT]) le_rfl
    (by rw [hτ]; simp [Function.update_apply, hIT, Ne.symm hIT])
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by omega)
  rw [hτ]
  apply WState.eq
  · funext j
    by_cases hjI : j = I
    · subst hjI; simp [Function.update_apply, hIT, hIh]
    · by_cases hjT : j = T
      · subst hjT; simp [Function.update_apply, hjI, hTh]
      · simp [Function.update_apply, hjI, hjT]
  · funext j
    by_cases hjT : j = T
    · subst hjT; simp [hT, sent, List.replicate_succ]
    · simp [Function.update_apply, hjT]
  · rfl
  · rfl

/-! ## Copies -/

/-- `Y := sent b` from `T = sent b`, every head back at `0`. -/
def sentCopy (T Y : Fin (ns + 1)) : WM ns nr := .seq (emit1 Y false) (.seq (innerW T Y) (rewSent Y))

theorem sentCopy_spec (T Y : Fin (ns + 1)) (hTY : T ≠ Y) (b : ℕ) (σ : WState ns nr) (hT : σ.st T = sent b)
    (hTh : σ.sh T = 0) (hY : σ.st Y = []) (hYh : σ.sh Y = 0) :
    WExec cap (sentCopy T Y) σ (σ.sets Y (sent b)) (13 * b + 15) := by
  have e1 := emit1_spec cap Y false σ (by rw [hY, hYh]; rfl)
  have e2 := innerW_spec cap T Y hTY b (appW σ Y [false]) (by simp [Function.update_apply, hTY, hT])
    (by simp [Function.update_apply, hTY, hTh]) (by simp)
  rw [appW_appW] at e2
  have e3 := rewSent_spec cap Y b (appW σ Y ([false] ++ List.replicate b true)) (by simp [hY, sent])
    (by simp [hY])
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases hjY : j = Y
    · subst hjY; simp [hYh]
    · simp [Function.update_apply, hjY]
  · funext j
    by_cases hjY : j = Y
    · subst hjY; simp [hY, sent]
    · simp [Function.update_apply, hjY]
  · rfl
  · rfl

/-- Back to the sentinel of `X`, stream `C` one cell per step. -/
def rewLock1 (X C : Fin (ns + 1)) : WM ns nr := .whs X (.seq (.bwd X) (.bwd C))

theorem rewLock1_spec (X C : Fin (ns + 1)) (hXC : X ≠ C) (c : ℕ) : ∀ (p : ℕ) (σ : WState ns nr),
    σ.st X = sent c → σ.sh X = p → p ≤ c → σ.sh C ≤ p →
    WExec cap (rewLock1 X C) σ ((σ.seth X 0).seth C 0) (5 * p + 1)
  | 0, σ, hs, hp, _, hI => by
    have hb : wbit σ X = false := by unfold wbit; rw [hs, hp, read_sent]; simp
    have e : (σ.seth X 0).seth C 0 = σ := by
      apply WState.eq
      · funext j
        by_cases hjC : j = C
        · subst hjC; simp; omega
        · by_cases hjX : j = X
          · subst hjX; simp [Function.update_apply, hjC, hp]
          · simp [Function.update_apply, hjC, hjX]
      · rfl
      · rfl
      · rfl
    rw [e]; exact WExec.mono (WExec.whsF hb) (by omega)
  | p + 1, σ, hs, hp, hc, hI => by
    have hb : wbit σ X = true := by unfold wbit; rw [hs, hp, read_sent]; simp; omega
    have e1 := WExec.bwd (cap := cap) X σ
    have e2 := WExec.bwd (cap := cap) C (σ.seth X (σ.sh X - 1))
    have ih := rewLock1_spec X C hXC c p ((σ.seth X (σ.sh X - 1)).seth C ((σ.seth X (σ.sh X - 1)).sh C - 1))
      (by simpa using hs) (by simp [Function.update_apply, hXC]; omega) (by omega)
      (by simp [Function.update_apply, Ne.symm hXC]; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) ih) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hjC : j = C
      · subst hjC; simp
      · by_cases hjX : j = X
        · subst hjX; simp [Function.update_apply, hjC]
        · simp [Function.update_apply, hjC, hjX]
    · rfl
    · rfl
    · rfl

/-- `C := 1^a` from `X = sent a`, every head back at `0`. -/
def plainCopy (X C : Fin (ns + 1)) : WM ns nr := .seq (.fwd X) (.seq (fillOnes X C) (.seq (.bwd X) (rewLock1 X C)))

theorem plainCopy_spec (X C : Fin (ns + 1)) (hXC : X ≠ C) (a : ℕ) (σ : WState ns nr) (hX : σ.st X = sent a)
    (hXh : σ.sh X = 0) (hC : σ.st C = []) (hCh : σ.sh C = 0) :
    WExec cap (plainCopy X C) σ (σ.sets C (List.replicate a true)) (12 * a + 7) := by
  have e1 := WExec.fwd (cap := cap) X σ
  rw [hXh] at e1
  have e2 := fillOnes_spec cap X C hXC a a (σ.seth X (0 + 1)) (by simpa using hX) (by simp; omega) (by simp)
    (by simp [Function.update_apply, Ne.symm hXC, hC, hCh])
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = (appW (σ.seth X (0 + 1)) C (List.replicate a true)).seth X (a + 1) := ⟨_, rfl⟩
  rw [← hτ] at e2
  have e3 := WExec.bwd (cap := cap) X τ
  have e4 := rewLock1_spec cap X C hXC a a (τ.seth X (τ.sh X - 1)) (by rw [hτ]; simp [Function.update_apply, hXC, hX])
    (by rw [hτ]; simp) le_rfl (by rw [hτ]; simp [Function.update_apply, Ne.symm hXC, hC])
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  rw [hτ]
  apply WState.eq
  · funext j
    by_cases hjC : j = C
    · subst hjC; simp [Function.update_apply, Ne.symm hXC, hCh]
    · by_cases hjX : j = X
      · subst hjX; simp [Function.update_apply, hjC, hXh]
      · simp [Function.update_apply, hjC, hjX]
  · funext j
    by_cases hjC : j = C
    · subst hjC; simp [hC]
    · simp [Function.update_apply, hjC]
  · rfl
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.S5T
