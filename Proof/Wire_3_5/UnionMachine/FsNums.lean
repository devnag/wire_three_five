import Proof.Wire_3_5.Primitive.Writers.GapNums
import Proof.Wire_3_5.UnionMachine.FsKit

/-! # C6, the FILTER setup, part 2: the regular filter's numbers from any length

"`prefixBits = ⌈log₂(32U)⌉`, `labelBits = max(prefixBits, ⌈log₂ M⌉)`, `fieldBits = ⌈log₂ M⌉ + 4`,
`walkLen = 2⌊errExp/4⌋ + 1`" and the seed length (filt:gap, P3:2019-2054, 2029-2030). `GapNums.gapNums_spec`
computes them from `U`, `M`, `errExp` for `M ≥ 2`; the FILTER setup (`FiltSetupSpec3`) takes every length, and the
THR writer's auxiliary filter has `M = 2Σ|carriers|` (possibly `0`). For `M ≤ 1`, `⌈log₂ M⌉ = 0`:
* **`lenBr`** / **`lenBr_spec`**: `K 7 := ⌈log₂ M⌉`, `K 5 := ⌈log₂ M⌉ + 4`, `K 4 := max (K 3) ⌈log₂ M⌉` at every `M`
  (the part `gB` when `M ≥ 2`, the constants otherwise);
* **`gapX`** / **`gapX_spec`**: the parts A, (the branch), C, S: `K 3 … K 6` the four numbers, `K 20 = seedBits`,
  `K 21 = 2^{seedBits}`, every other register as at entry, at every length.

Paper quantities of the main type: `GapParams.prefixBits`, `labelBits`, `fieldBits`, `walkLen`, `seedBits`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsNums
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimAsm.FiltNum NearCubicWires.WireExponent3_5.PrimAsm.GapNums
open NearCubicWires.WireExponent3_5.UnionMachine.BinW (bsetv_self)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## The length branch -/

/-- `F := M - 1`; if `M ≥ 2` the part `gB`, else `K 5 := 4`, `K 4 := K 3` (`⌈log₂ M⌉ = 0`). -/
def lenBr (K : Fin 32 ↪ Fin nr) (F T : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (K 1) F T) (.seq (.dec F) (.ifr F (.seq (WM.clear F) (gB K))
    (.seq (WM.clear F) (.seq (StarNums.incN (K 5) 4) (FinalPass.Hash4.wcopyR (K 3) (K 4) (K 14))))))

theorem lenBr_spec (K : Fin 32 ↪ Fin nr) (F T : Fin nr) (hF : ∀ i, K i ≠ F) (hT : ∀ i, K i ≠ T) (hFT : F ≠ T)
    (σ : WState ns nr) (M PB : ℕ) (hM0 : σ.val (K 1) = M) (hP0 : σ.val (K 3) = PB)
    (hz : ∀ i : Fin 32, 4 ≤ i.val → σ.val (K i) = 0) (hF0 : σ.val F = 0) (hT0 : σ.val T = 0) (hc1 : 1 ≤ cap)
    (hMc : M + 8 ≤ cap) (hPc : PB + 4 ≤ cap) :
    WExec cap (lenBr K F T) σ (((σ.setv (K 7) (Nat.clog 2 M)).setv (K 5) (Nat.clog 2 M + 4)).setv (K 4)
      (max PB (Nat.clog 2 M))) (30 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  have h1 := copy1 cap (K 1) F T (hF 1) (hT 1) hFT M σ hM0 hF0 hT0 (by omega)
  have h2 := dec1 cap F M (σ.setv F M) (by simp) (by omega)
  have h3 : WExec cap (WM.clear F) ((σ.setv F M).setv F (M - 1)) σ (UnaryPow.sq cap) :=
    WExec.cast cap (clear1 cap F (M - 1) ((σ.setv F M).setv F (M - 1)) (by simp) (by omega))
      (by rw [wsetv_setv, wsetv_setv, bsetv_self σ F 0 hF0]) le_rfl
  by_cases hM : 2 ≤ M
  · have h4 := gB_run cap K σ M PB hM0 hM hP0 hz hc1 hMc (by omega)
    have hne : ((σ.setv F M).setv F (M - 1)).val F ≠ 0 := by simp; omega
    exact WExec.mono (WExec.seq h1 (WExec.seq h2 (WExec.ifrT hne (WExec.seq h3 h4)))) (by omega)
  · have hC : Nat.clog 2 M = 0 := Nat.clog_of_right_le_one (by omega) 2
    have h4 := incN0 cap (K 5) 4 σ (hz 5 (by decide)) (by omega)
    have h5 := copy1 cap (K 3) (K 4) (K 14) (fun h => absurd (K.injective h) (by decide))
      (fun h => absurd (K.injective h) (by decide)) (fun h => absurd (K.injective h) (by decide)) PB (σ.setv (K 5) 4)
      (by rw [wsetv_val_ne _ _ (fun h => absurd (K.injective h) (by decide)), hP0])
      (by rw [wsetv_val_ne _ _ (fun h => absurd (K.injective h) (by decide)), hz 4 (by decide)])
      (by rw [wsetv_val_ne _ _ (fun h => absurd (K.injective h) (by decide)), hz 14 (by decide)]) (by omega)
    have hz0 : ((σ.setv F M).setv F (M - 1)).val F = 0 := by simp; omega
    refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.ifrF hz0 (WExec.seq h3 (WExec.seq h4 h5))))) ?_
      (by omega)
    rw [hC, bsetv_self σ (K 7) 0 (hz 7 (by decide)), Nat.zero_add, Nat.max_zero]

/-! ## The four numbers and the seed length, at every length -/

/-- **The regular filter's numbers** (the parts A, C, S around the length branch). -/
def gapX (K : Fin 32 ↪ Fin nr) (F T : Fin nr) : WM ns nr :=
  .seq (filtA K) (.seq (lenBr K F T) (.seq (filtC K) (gS K)))

theorem gapX_spec (K : Fin 32 ↪ Fin nr) (F T : Fin nr) (hF : ∀ i, K i ≠ F) (hT : ∀ i, K i ≠ T) (hFT : F ≠ T)
    (σ : WState ns nr) (P : Filters.GapParams) (hB0 : σ.val (K 0) = P.cap) (hM0 : σ.val (K 1) = P.len)
    (hE0 : σ.val (K 2) = P.errExp) (hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (K i) = 0) (hF0 : σ.val F = 0)
    (hT0 : σ.val T = 0) (hB1 : 1 ≤ P.cap) (hc1 : 1 ≤ cap) (hBc : P.cap * 32 + 2 ≤ cap) (hMc : P.len + 8 ≤ cap)
    (hEc : P.errExp + 4 ≤ cap) (hsc : 2 ^ (P.seedBits + 1) ≤ cap)
    (hlc : P.labelBits + P.fieldBits + P.walkLen + 512 ≤ cap) :
    WExec cap (gapX K F T) σ ((((((σ.setv (K 3) P.prefixBits).setv (K 4) P.labelBits).setv (K 5) P.fieldBits).setv
      (K 6) P.walkLen).setv (K 20) P.seedBits).setv (K 21) (2 ^ P.seedBits)) (120 * UnaryPow.sq cap) := by
  have hsq := UnaryPow.sq_ge cap
  obtain ⟨PB, hPB⟩ : ∃ v, v = Nat.clog 2 (32 * P.cap) := ⟨_, rfl⟩
  obtain ⟨CL, hCL⟩ : ∃ v, v = Nat.clog 2 P.len := ⟨_, rfl⟩
  have ePB : P.prefixBits = PB := hPB.symm
  have eLB : P.labelBits = max PB CL := by rw [hPB, hCL]; rfl
  have eFB : P.fieldBits = CL + 4 := by rw [hCL]; rfl
  have eWL : P.walkLen = 2 * (P.errExp / 4) + 1 := rfl
  have hPc : PB ≤ cap := by
    have : P.prefixBits ≤ P.labelBits := le_max_left _ _
    rw [← ePB]; omega
  have hPB1 : 1 ≤ PB := by rw [hPB]; exact Nat.clog_pos (by norm_num) (by omega)
  have hmx : 1 ≤ max PB CL := le_trans hPB1 (le_max_left _ _)
  have hCc : CL ≤ cap := by rw [eFB] at hlc; omega
  have hA := filtA_spec cap K σ P.cap hB0 hz hB1 hBc
  rw [← hPB] at hA
  have hB := lenBr_spec cap K F T hF hT hFT (σ.setv (K 3) PB) P.len PB
    (by rw [wsetv_val_ne _ _ (fun h => absurd (K.injective h) (by decide)), hM0]) (by simp)
    (fun i hi => by
      have hi3 : K i ≠ K 3 := fun h => absurd (K.injective h) (by intro e; subst e; simp at hi)
      rw [wsetv_val_ne _ _ hi3, hz i (by omega)])
    (by rw [wsetv_val_ne _ _ (Ne.symm (hF 3)), hF0]) (by rw [wsetv_val_ne _ _ (Ne.symm (hT 3)), hT0]) hc1 hMc
    (by rw [eLB] at hlc; have := le_max_left PB CL; omega)
  rw [← hCL] at hB
  have hC := filtC_spec cap K ((((σ.setv (K 3) PB).setv (K 7) CL).setv (K 5) (CL + 4)).setv (K 4) (max PB CL))
    P.errExp CL (by simp [hE0]) (by simp) (by simp [hz]) (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn7 : i ≠ 7 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      simp [Function.update_apply, hn3, hn7, hn5, hn4, hz i (by omega)]) hc1 hEc hCc
  have hS := gS_run cap K (((((((σ.setv (K 3) PB).setv (K 7) CL).setv (K 5) (CL + 4)).setv (K 4) (max PB CL)).setv
      (K 6) (2 * (P.errExp / 4) + 1)).setv (K 7) 0)) (max PB CL) (CL + 4) (2 * (P.errExp / 4) + 1)
    (by simp) (by simp) (by simp) hmx (by omega)
    (fun i hi => by
      have hn3 : i ≠ 3 := by intro h; subst h; simp at hi
      have hn7 : i ≠ 7 := by intro h; subst h; simp at hi
      have hn5 : i ≠ 5 := by intro h; subst h; simp at hi
      have hn4 : i ≠ 4 := by intro h; subst h; simp at hi
      have hn6 : i ≠ 6 := by intro h; subst h; simp at hi
      rcases hi with hi | hi
      · simp [Function.update_apply, hn3, hn7, hn5, hn4, hn6, hz i (by omega)]
      · simp [Function.update_apply, hn3, hn7, hn5, hn4, hn6, hz i (by omega)])
    hc1 (by rw [← eLB, ← eFB, ← eWL, ← seedBits_eq]; exact hsc) (by rw [← eLB, ← eFB, ← eWL]; exact hlc)
  refine WExec.cast cap (WExec.seq hA (WExec.seq hB (WExec.seq hC hS))) ?_ (by omega)
  rw [ePB, eLB, eFB, eWL, seedBits_eq, eLB, eFB, eWL]
  apply WState.eq
  · rfl
  · rfl
  · funext r
    simp only [WState.setv_val, Function.update_apply]
    by_cases h7 : r = K 7
    · subst h7
      simp [hz 7 (by decide)]
    · simp only [h7, if_false]
      by_cases h4 : r = K 4
      · subst h4; simp
      · simp [h4]
  · rfl

end NearCubicWires.WireExponent3_5.UnionMachine.FsNums
