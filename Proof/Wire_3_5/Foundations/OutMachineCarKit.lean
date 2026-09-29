import Proof.Wire_3_5.Foundations.OutMachineCarM2b
import Proof.Wire_3_5.Foundations.OutMachineP1
import Proof.Wire_3_5.Primitive.Writers.SBErase

/-! # The output machine carrier phase, part 4: the generic kit (count, pad, erase a list)

Word-program pieces for the carrier phase's outer programs, generic in the layout:

* **`cntF_spec`**: `K := |w|` from a framed word `frame w` (P1's `cntW`), the head back at `0`;
* `pcO`, **`wenc_padO`**, **`step_up`**: a run whose registers are `0` at both ends, proved at a small capacity,
  is a run at any larger capacity (registers padded by `0`s, `Step.pad`);
* `eraseOne`, **`eraseList`**, `setsAll`, **`eraseList_spec`**: every stream of a list, head at `0` and length at
  most `T`, becomes `0^T` (`SBErase.eraseW`, `T` copied from a master register each time).

Paper quantity of the main type: none beyond the machine model (the phase's junk-free exit, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarKit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SBErase (eraseW erase_spec)

variable {ns nr : ℕ} (cap : ℕ)

/-- **`K := |w|`** from `frame w` on `A`. -/
theorem cntF_spec (A : Fin (ns + 1)) (R K : Fin nr) (hRK : R ≠ K) (w : List Bool) (σ : WState ns nr)
    (hA : σ.st A = frame w) (hh : σ.sh A = 0) (hR : σ.val R = 0) (hK : σ.val K = 0) (hc : 2 * w.length ≤ cap) :
    WExec cap (P1.cntW A R K) σ (σ.setv K w.length) (27 * w.length + 3) := by
  have l := P1.cntLoop_spec cap A R K hRK [] w [] σ (by rw [hA, P1.frame_split]) (by simp [hh])
    (by simp [hK]; omega) (by simp [hR]; omega)
  simp only [List.length_nil, Nat.zero_add, hK, hR] at l
  have r := wrewind_spec cap A R (2 * w.length) (((σ.seth A (2 * w.length)).setv K w.length).setv R (2 * w.length))
    (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq l r) ?_ (by omega)
  refine WState.eq ?_ rfl ?_ rfl
  · funext j
    simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [hh]
    · rfl
  · funext j
    simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs with h1 h2 <;> (try subst_vars) <;> simp_all

/-! ## Raising the capacity -/

/-- The padding of a register tape to capacity `c'`. -/
def pcO (ns nr c' : ℕ) (j : Fin (ns + 2 + nr)) : ℕ := if ns + 2 ≤ j.val then c' + 1 else 0

theorem wenc_padO (c c' : ℕ) (hc : c ≤ c') (σ : WState ns nr) (hv : ∀ r, σ.val r = 0) :
    (fun j => ZeroPadding.pad (pcO ns nr c' j) ((wenc c σ).A j)) = (wenc c' σ).A := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · have h0 : pcO ns nr c' (sTape (nr := nr) i) = 0 := by
      unfold pcO; rw [if_neg]; rw [sTape_val]; have := i.isLt; split_ifs <;> omega
    rw [h0, ZeroPadding.pad_zero, wenc_A_s, wenc_A_s]
  · have h0 : pcO ns nr c' (cTape (ns := ns) (nr := nr)) = 0 := by
      unfold pcO; rw [if_neg]; rw [cTape_val]; omega
    rw [h0, ZeroPadding.pad_zero, wenc_A_c, wenc_A_c]
  · have h1 : pcO ns nr c' (rTape (ns := ns) r) = c' + 1 := by
      unfold pcO; rw [if_pos]; rw [rTape_val]; omega
    rw [h1, wenc_A_r, wenc_A_r, hv, regTape_zero, regTape_zero]
    unfold ZeroPadding.pad
    rw [List.length_replicate, ← List.replicate_add]
    congr 1
    omega

/-- **A run at a small capacity is a run at any larger one** (registers `0` at both ends). -/
theorem step_up {s : ℕ} (M : Machine (ns + 2 + nr) s) (n c c' : ℕ) (hc : c ≤ c') (σ τ : WState ns nr)
    (hσ : ∀ r, σ.val r = 0) (hτ : ∀ r, τ.val r = 0)
    (h : Step M n (wenc c σ).H (wenc c σ).A (wenc c τ).H (wenc c τ).A) :
    Step M n (wenc c' σ).H (wenc c' σ).A (wenc c' τ).H (wenc c' τ).A := by
  have hp := h.pad (pcO ns nr c')
  rw [wenc_padO c c' hc σ hσ, wenc_padO c c' hc τ hτ] at hp
  exact hp

/-! ## Erasing a list of streams -/

/-- One stream to `0^T`: copy the master `T` into `c`, erase. -/
def eraseOne (s : Fin (ns + 1)) (M c d t : Fin nr) : WM ns nr := .seq (UnionMachine.BinW.dupR M c t) (eraseW s c d)

/-- Every stream of a list to `0^T`. -/
def eraseList (M c d t : Fin nr) : List (Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | s :: l => .seq (eraseOne s M c d t) (eraseList M c d t l)

/-- `σ` with the streams of `l` set to `w`. -/
def setsAll (σ : WState ns nr) (l : List (Fin (ns + 1))) (w : List Bool) : WState ns nr :=
  ⟨σ.sh, fun i => if i ∈ l then w else σ.st i, σ.val, σ.cell⟩

theorem eraseList_spec (M c d t : Fin nr) (hMc : M ≠ c) (hMd : M ≠ d) (hMt : M ≠ t) (hcd : c ≠ d) (hct : c ≠ t)
    (hdt : d ≠ t) (T : ℕ) (hT : T ≤ cap) :
    ∀ (l : List (Fin (ns + 1))) (σ : WState ns nr), l.Nodup → (∀ s ∈ l, σ.sh s = 0 ∧ (σ.st s).length ≤ T) →
      σ.val M = T → σ.val c = 0 → σ.val d = 0 → σ.val t = 0 →
      WExec cap (eraseList M c d t l) σ (setsAll σ l (List.replicate T false)) (l.length * (34 * T + 8))
  | [], σ, _, _, _, _, _, _ => by
    refine WExec.cast cap (WExec.skip σ) ?_ (by simp)
    exact WState.eq rfl (by funext i; simp [setsAll]) rfl rfl
  | s :: l, σ, hnd, hl, hM, hc, hd, ht => by
    have hs := hl s (by simp)
    have h1 := UnionMachine.BinW.dupR_spec cap M c t hMc hMt hct σ T hM hc ht hT
    have h2 := erase_spec cap s c d hcd T (σ.setv c T) (by simp) (by simp [Function.update_of_ne (Ne.symm hcd), hd])
      (by simp [hs.1]) (by simp [hs.2]) hT
    have e1 : ((σ.setv c T).sets s (List.replicate T false)).setv c 0 = σ.sets s (List.replicate T false) := by
      refine WState.eq rfl rfl ?_ rfl
      funext j
      simp only [WState.setv_val, WState.sets_val, Function.update_apply]
      split_ifs with h
      · subst h; exact hc.symm
      · rfl
    rw [e1] at h2
    have hnd' := List.nodup_cons.1 hnd
    have ih := eraseList_spec M c d t hMc hMd hMt hcd hct hdt T hT l (σ.sets s (List.replicate T false)) hnd'.2
      (fun s' hs' => by
        have hne : s' ≠ s := fun h => hnd'.1 (h ▸ hs')
        have := hl s' (by simp [hs'])
        simp [Function.update_of_ne hne, this.1, this.2]) hM hc hd ht
    refine WExec.cast cap (WExec.seq (WExec.seq h1 h2) ih) ?_ (by simp [Nat.succ_mul]; omega)
    refine WState.eq rfl ?_ rfl rfl
    funext i
    by_cases h1 : i ∈ l
    · simp [setsAll, h1]
    · by_cases h2 : i = s
      · subst h2; simp [setsAll, h1]
      · simp [setsAll, h1, h2, Function.update_of_ne h2]


end NearCubicWires.WireExponent3_5.FinalPass.Out.CarKit
