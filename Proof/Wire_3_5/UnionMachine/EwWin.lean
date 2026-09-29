import Proof.Wire_3_5.UnionMachine.EwLevel

/-! # C6, e/W_j, part 3: the fixed hash's window records

"The level windows `W_j = 16t + 20(⌊√(t·B_*)⌋ + 1)/2^{⌊j/2⌋} + 20`" (filt:majorant, P3:2150-2157) as C5's final pass
reads them (stage 4's `winWord`): the records `winRec J W j = true :: unary(pow W'_j) ++ unary W'_j` for the levels
`J, …, 0` (`W'_J = 0`), **`Joins.winRecs`**-shaped. From `t`, `B_*`, `J` in registers (kept) on a blank stream:
`s := ⌊√(t·B_*)⌋` (`EwKit.sqrtF`), the top record, the `J` records below it (`EwLevel.lvBody` in a flag loop), the head
back at `0`, the scratch back at `0` (**`winW_spec`**); the records are the fixed hash's (**`winList_eq`**).

Paper quantity of the main type: the fixed hash's level windows `W_j` (filt:majorant) as stage 4's records. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwWin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.EwLevel
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (dupR bsetv_self)

variable {ns nr : ℕ} (cap : ℕ)

/-- The level machinery's registers inside the window block: `t = 0`, `s = 3`, the counter `4`, scratch `5 … 21`. -/
def vmap : Fin 20 ↪ Fin 32 := ⟨![0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩
/-- The square root's registers: `X1 = 22`, `s = 3`, scratch `23 … 27`. -/
def rmap : Fin 7 ↪ Fin 32 := ⟨![22, 3, 23, 24, 25, 26, 27], by decide⟩

@[simp] theorem vmap_apply (i : Fin 20) :
    vmap i = ![0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21] i := rfl
@[simp] theorem rmap_apply (i : Fin 7) : rmap i = ![22, 3, 23, 24, 25, 26, 27] i := rfl

/-- The top level's record: `W'_J = 0`, `pow 0 = 1`. -/
def topRec : List Bool := [true, true, false, false]

/-- **The window records** from `t`, `B_*`, `J`. -/
def winList (t B J : ℕ) : List Bool := topRec ++ recsDown t (Nat.sqrt (t * B)) J J

section Win
variable (O : Fin (ns + 1)) (W : Fin 32 ↪ Fin nr)

/-- The window block's first part: `X1 := t·B + 1`, `s := ⌊√(t·B)⌋`, the top record, the counter `:= J`. -/
def winA : WM ns nr :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (FsKit.mulR (W 0) (W 1) (W 22) (W 29) (W 30)) (.inc (W 22)))
    (EwKit.sqrtF (rmap.trans W))) (emitC O (W 28) true)) (emitC O (W 28) true)) (emitC O (W 28) false))
    (emitC O (W 28) false)) (dupR (W 2) (W 4) (W 29))

/-- The state after the first part. -/
def stTop (σ : WState ns nr) (t B J : ℕ) : WState ns nr :=
  (((((σ.setv (W 22) (B * t + 1)).setv (W 3) (Nat.sqrt (B * t))).sets O topRec).seth O 4).setv (W 28) 4).setv
    (W 4) J

theorem winA_spec (σ : WState ns nr) (t B J : ℕ) (h0 : σ.val (W 0) = t) (h1 : σ.val (W 1) = B)
    (h2 : σ.val (W 2) = J) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (W i) = 0) (hO : σ.st O = [])
    (hOh : σ.sh O = 0) (hcap : 2 * (B * t + 2) * (B * t + 2) + t + B + J + 20 ≤ cap) :
    ∃ n, WExec cap (winA O W) σ (stTop O W σ t B J) n ∧
      n ≤ 1000 * (B * t + 2) * (B * t + 2) * (B * t + 2) + 40 * (B + 1) * (t + 1) + 20 * J + 100 := by
  have hne : ∀ {i k : Fin 32}, i ≠ k → W i ≠ W k := fun h => W.injective.ne h
  have hW : ∀ i k : Fin 32, W i = W k ↔ i = k := fun i k => W.injective.eq_iff
  have hbt : B * t ≤ 2 * (B * t + 2) * (B * t + 2) := by
    obtain ⟨x, hx⟩ : ∃ x, x = B * t := ⟨_, rfl⟩
    rw [← hx]; nlinarith
  have c1 := FsKit.mulR_spec cap (W 0) (W 1) (W 22) (W 29) (W 30) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ t B h0 h1 (hz 29 (by decide)) (hz 30 (by decide)) (by rw [hz 22 (by decide)]; omega)
    (by omega) (by omega)
  have c2 := WExec.seq c1 (WExec.inc (cap := cap) (W 22) _ (by simp [hz 22 (by decide)]; omega))
  obtain ⟨n3, e3, hn3⟩ := EwKit.sqrtF_spec cap (rmap.trans W)
    ((σ.setv (W 22) (σ.val (W 22) + B * t)).setv (W 22) ((σ.setv (W 22) (σ.val (W 22) + B * t)).val (W 22) + 1))
    (B * t) (by simp [hW, hz 22 (by decide)]) (by simp [hW, hz 3 (by decide)]) (by simp [hW, hz 23 (by decide)])
    (by simp [hW, hz 24 (by decide)]) (by simp [hW, hz 25 (by decide)]) (by simp [hW, hz 26 (by decide)])
    (by simp [hW, hz 27 (by decide)]) (by omega)
  have c3 := WExec.seq c2 e3
  have c4 := WExec.seq c3 (emitC_spec cap O (W 28) true _ (by simp [hO, hOh]) (by simp [hW, hz 28 (by decide)]; omega))
  have c5 := WExec.seq c4 (emitC_spec cap O (W 28) true _ (by simp [hO, hOh]) (by simp [hW, hz 28 (by decide)]; omega))
  have c6 := WExec.seq c5 (emitC_spec cap O (W 28) false _ (by simp [hO, hOh]) (by simp [hW, hz 28 (by decide)]; omega))
  have c7 := WExec.seq c6 (emitC_spec cap O (W 28) false _ (by simp [hO, hOh]) (by simp [hW, hz 28 (by decide)]; omega))
  have c8 := WExec.seq c7 (BinW.dupR_spec cap (W 2) (W 4) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) _ J (by simp [hW, h2]) (by simp [hW, hz 4 (by decide)]) (by simp [hW, hz 29 (by decide)])
    (by omega))
  refine ⟨_, WExec.cast cap c8 ?_ le_rfl, ?_⟩
  · clear c1 c2 c3 c4 c5 c6 c7 c8 e3
    apply WState.eq
    · funext q
      by_cases hq : q = O
      · subst hq; simp [stTop, hOh]
      · simp [stTop, hq]
    · funext q
      by_cases hq : q = O
      · subst hq; simp [stTop, hO, topRec]
      · simp [stTop, hq]
    · funext q
      by_cases q22 : q = W 22
      · subst q22; simp [stTop, hW, hz 22 (by decide)]
      · by_cases q3 : q = W 3
        · subst q3; simp [stTop, hW]
        · by_cases q28 : q = W 28
          · subst q28; simp [stTop, hW, hz 28 (by decide)]
          · by_cases q4 : q = W 4
            · subst q4; simp [stTop, hW]
            · simp [stTop, Function.update_apply, q22, q3, q28, q4]
    · simp [stTop]
  · clear c1 c2 c3 c4 c5 c6 c7 c8 e3
    have hBt : B * (18 * t + 7) + 18 * B ≤ 40 * (B + 1) * (t + 1) := by nlinarith
    omega

end Win

end NearCubicWires.WireExponent3_5.UnionMachine.EwWin
