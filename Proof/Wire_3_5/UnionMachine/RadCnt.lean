import Proof.Wire_3_5.UnionMachine.RadTab

/-! # RADIX, stage 5a (4): one digit's population count, read in place (P3:2598-2599)

The digit word `digsWord ls = ls.flatMap gisWord` (`DigsW`'s format) is read in place: at digit `d`'s start the stream
holds `gisWord gis ++ rest` from its head. **`cntP`** counts the digit's pool indices (`L_d = |gis|`, the block writer's
first input) and returns the head to the digit's start; **`skipG`** moves the head past the digit.

* `skipU_spec` (a unary field's ones), `itemC_spec` (one index `true :: 1^gi 0`), `cntLoop_spec` (all of them);
* **`cntP_spec`**, **`skipG_spec`**.

Paper quantity of the main type: the digit populations' sizes `|gis_d|` (P3:2598-2599). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadCnt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

variable {ns nr : ℕ} (cap : ℕ)

/-- One index's word. -/
def itemW (gi : ℕ) : List Bool := true :: (List.replicate gi true ++ [false])

theorem gisWord_eq (gis : List ℕ) : gisWord gis = gis.flatMap itemW ++ [false] := rfl

/-- Skip the ones under the head of `i`, counting in `c`. -/
def skipU (i : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .whs i (WM.fwdC i c)

theorem skipU_spec (i : Fin (ns + 1)) (c : Fin nr) : ∀ (n : ℕ) (σ : WState ns nr),
    (∀ k < n, readTapeBit (σ.st i) (σ.sh i + k) = true) → readTapeBit (σ.st i) (σ.sh i + n) = false →
    σ.val c + n ≤ cap →
    WExec cap (skipU i c) σ ((σ.seth i (σ.sh i + n)).setv c (σ.val c + n)) (7 * n + 1)
  | 0, σ, _, hend, _ => by
    have e : (σ.seth i (σ.sh i + 0)).setv c (σ.val c + 0) = σ := WState.eq (by simp) rfl (by simp) rfl
    rw [e]
    exact WExec.whsF (by simpa [wbit] using hend)
  | n + 1, σ, hones, hend, hc => by
    have h1 := wfwdC_spec cap i c σ (by omega)
    set τ := (σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1) with hτ
    have ih := skipU_spec i c n τ (fun k hk => by
        simp only [τ, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show σ.sh i + 1 + k = σ.sh i + (k + 1) by omega]; exact hones (k + 1) (by omega))
      (by simp only [τ, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
          rw [show σ.sh i + 1 + n = σ.sh i + (n + 1) by omega]; exact hend)
      (by simp [τ]; omega)
    refine WExec.cast cap (WExec.whsT (by simpa [wbit] using hones 0 (by omega)) h1 ih) ?_ (by omega)
    apply WState.eq
    · funext j; by_cases hj : j = i
      · subst hj; simp [τ]; omega
      · simp [τ, Function.update_apply, hj]
    · rfl
    · funext q; by_cases hq : q = c
      · subst hq; simp [τ]; omega
      · simp [τ, Function.update_apply, hq]
    · rfl

/-- One index: the marker, its ones, its `0`; `Lr += 1`. -/
def itemC (i : Fin (ns + 1)) (c Lr : Fin nr) : WM ns nr :=
  .seq (WM.fwdC i c) (.seq (skipU i c) (.seq (WM.fwdC i c) (.inc Lr)))

theorem itemC_spec (i : Fin (ns + 1)) (c Lr : Fin nr) (hcL : c ≠ Lr) (gi : ℕ) (rest : List Bool) (σ : WState ns nr)
    (hd : (σ.st i).drop (σ.sh i) = itemW gi ++ rest) (hc : σ.val c + gi + 2 ≤ cap) (hL : σ.val Lr < cap) :
    WExec cap (itemC i c Lr) σ
      (((σ.seth i (σ.sh i + (gi + 2))).setv c (σ.val c + (gi + 2))).setv Lr (σ.val Lr + 1)) (7 * gi + 17) := by
  have h1 := wfwdC_spec cap i c σ (by omega)
  set σ1 := (σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1) with hσ1
  have hd1 : (σ1.st i).drop (σ1.sh i) = List.replicate gi true ++ false :: rest := by
    simp only [σ1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
    exact dropSucc (a := true) (by rw [hd]; simp [itemW])
  obtain ⟨o1, e1⟩ := onesDrop hd1
  have h2 := skipU_spec cap i c gi σ1 o1 e1 (by simp [σ1]; omega)
  set σ2 := (σ1.seth i (σ1.sh i + gi)).setv c (σ1.val c + gi) with hσ2
  have h3 := wfwdC_spec cap i c σ2 (by simp [σ2, σ1]; omega)
  set σ3 := (σ2.seth i (σ2.sh i + 1)).setv c (σ2.val c + 1) with hσ3
  have h4 := WExec.inc (cap := cap) Lr σ3 (by simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hcL]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [σ3, σ2, σ1]; omega
    · simp [σ3, σ2, σ1, Function.update_apply, hj]
  · rfl
  · funext q; by_cases hq : q = Lr
    · subst hq; simp [σ3, σ2, σ1, Function.update_apply, Ne.symm hcL]
    · by_cases hq2 : q = c
      · subst hq2; simp [σ3, σ2, σ1, Function.update_apply, hq]; omega
      · simp [σ3, σ2, σ1, Function.update_apply, hq, hq2]
  · rfl

/-- The item loop: all indices of a digit, up to its closing `0`. -/
def cntLoop (i : Fin (ns + 1)) (c Lr : Fin nr) : WM ns nr := .whs i (itemC i c Lr)

/-- The item loop's cost. -/
def cntCost (gis : List ℕ) : ℕ := (gis.map fun gi => 7 * gi + 19).sum + 1

theorem cntLoop_spec (i : Fin (ns + 1)) (c Lr : Fin nr) (hcL : c ≠ Lr) (rest : List Bool) :
    ∀ (gis : List ℕ) (σ : WState ns nr), (σ.st i).drop (σ.sh i) = gisWord gis ++ rest →
      σ.val c + (gis.flatMap itemW).length ≤ cap → σ.val Lr + gis.length < cap →
      WExec cap (cntLoop i c Lr) σ
        (((σ.seth i (σ.sh i + (gis.flatMap itemW).length)).setv c (σ.val c + (gis.flatMap itemW).length)).setv Lr
          (σ.val Lr + gis.length)) (cntCost gis)
  | [], σ, hd, _, _ => by
    have hb : wbit σ i = false := by
      unfold wbit; rw [← Nat.add_zero (σ.sh i), readDrop, hd]; simp [gisWord, readTapeBit]
    have e : ((σ.seth i (σ.sh i + (([] : List ℕ).flatMap itemW).length)).setv c
        (σ.val c + (([] : List ℕ).flatMap itemW).length)).setv Lr (σ.val Lr + ([] : List ℕ).length) = σ :=
      WState.eq (by simp) rfl (by simp) rfl
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp [cntCost])
  | gi :: gis, σ, hd, hc, hL => by
    have hd' : (σ.st i).drop (σ.sh i) = itemW gi ++ (gisWord gis ++ rest) := by
      rw [hd, gisWord_eq, gisWord_eq]; simp [List.append_assoc]
    have hb : wbit σ i = true := by
      unfold wbit; rw [← Nat.add_zero (σ.sh i), readDrop, hd']; simp [itemW, readTapeBit]
    have hlen : (itemW gi).length = gi + 2 := by simp [itemW]
    have hfl : ((gi :: gis).flatMap itemW).length = (gi + 2) + (gis.flatMap itemW).length := by
      simp [List.flatMap_cons, hlen]
    have h1 := itemC_spec cap i c Lr hcL gi (gisWord gis ++ rest) σ hd' (by rw [hfl] at hc; omega)
      (by simp at hL; omega)
    set σ1 := ((σ.seth i (σ.sh i + (gi + 2))).setv c (σ.val c + (gi + 2))).setv Lr (σ.val Lr + 1) with hσ1
    have hd1 : (σ1.st i).drop (σ1.sh i) = gisWord gis ++ rest := by
      simp only [σ1, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self]
      rw [← hlen]; exact dropAppend hd'
    have vc1 : σ1.val c = σ.val c + (gi + 2) := by simp [σ1, Function.update_apply, hcL]
    have vL1 : σ1.val Lr = σ.val Lr + 1 := by simp [σ1]
    have hgl : (gi :: gis).length = gis.length + 1 := rfl
    have ih := cntLoop_spec i c Lr hcL rest gis σ1 hd1
      (by rw [vc1]; rw [hfl] at hc; omega) (by rw [vL1]; rw [hgl] at hL; omega)
    refine WExec.cast cap (WExec.whsT hb h1 ih) ?_ (by simp [cntCost]; omega)
    apply WState.eq
    · funext j; by_cases hj : j = i
      · subst hj; simp [σ1, hfl]; omega
      · simp [σ1, Function.update_apply, hj]
    · rfl
    · funext q; by_cases hq : q = Lr
      · subst hq; simp [σ1, Function.update_apply, Ne.symm hcL]; omega
      · by_cases hq2 : q = c
        · subst hq2; simp [σ1, Function.update_apply, hq, hfl]; omega
        · simp [σ1, Function.update_apply, hq, hq2]
    · rfl

/-- **The digit's count**: `Lr += |gis|`, the head back at the digit's start (by `c`). -/
def cntP (i : Fin (ns + 1)) (c Lr : Fin nr) : WM ns nr := .seq (cntLoop i c Lr) (WM.rewind i c)

theorem cntP_spec (i : Fin (ns + 1)) (c Lr : Fin nr) (hcL : c ≠ Lr) (gis : List ℕ) (rest : List Bool)
    (σ : WState ns nr) (hd : (σ.st i).drop (σ.sh i) = gisWord gis ++ rest) (hc0 : σ.val c = 0)
    (hc : (gis.flatMap itemW).length ≤ cap) (hL : σ.val Lr + gis.length < cap) :
    WExec cap (cntP i c Lr) σ (σ.setv Lr (σ.val Lr + gis.length))
      (cntCost gis + 1 + (5 * (gis.flatMap itemW).length + 1)) := by
  have h1 := cntLoop_spec cap i c Lr hcL rest gis σ hd (by omega) hL
  rw [hc0, Nat.zero_add] at h1
  have h2 := wrewind_spec cap i c (gis.flatMap itemW).length
    (((σ.seth i (σ.sh i + (gis.flatMap itemW).length)).setv c (gis.flatMap itemW).length).setv Lr
      (σ.val Lr + gis.length)) (by simp [Function.update_apply, hcL])
      (by rw [show (((σ.seth i (σ.sh i + (gis.flatMap itemW).length)).setv c (gis.flatMap itemW).length).setv Lr
            (σ.val Lr + gis.length)).val c = (gis.flatMap itemW).length by simp [Function.update_apply, hcL]]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_apply, hj]
  · rfl
  · funext q; by_cases hq : q = c
    · subst hq; simp [Function.update_apply, hcL, hc0]
    · simp [Function.update_apply, hq]
  · rfl

/-- **Past the digit**: the item loop (counting into `Lr`, cleared after) and its closing `0`. -/
def skipG (i : Fin (ns + 1)) (c Lr : Fin nr) : WM ns nr :=
  .seq (cntLoop i c Lr) (.seq (.fwd i) (.seq (WM.clear c) (WM.clear Lr)))

theorem skipG_spec (i : Fin (ns + 1)) (c Lr : Fin nr) (hcL : c ≠ Lr) (gis : List ℕ) (rest : List Bool)
    (σ : WState ns nr) (hd : (σ.st i).drop (σ.sh i) = gisWord gis ++ rest) (hc0 : σ.val c = 0) (hL0 : σ.val Lr = 0)
    (hc : (gis.flatMap itemW).length ≤ cap) (hL : gis.length < cap) :
    WExec cap (skipG i c Lr) σ (σ.seth i (σ.sh i + (gisWord gis).length))
      (cntCost gis + 1 + (1 + 1 + ((3 * (gis.flatMap itemW).length + 1) + 1 + (3 * gis.length + 1)))) := by
  have h1 := cntLoop_spec cap i c Lr hcL rest gis σ hd (by omega) (by omega)
  rw [hc0, hL0, Nat.zero_add, Nat.zero_add] at h1
  set σ1 := ((σ.seth i (σ.sh i + (gis.flatMap itemW).length)).setv c (gis.flatMap itemW).length).setv Lr gis.length
    with hσ1
  have h2 := WExec.fwd (cap := cap) i σ1
  have h3 := wclear_spec cap c (gis.flatMap itemW).length (σ1.seth i (σ1.sh i + 1))
    (by simp [σ1, Function.update_apply, hcL])
    (by rw [show (σ1.seth i (σ1.sh i + 1)).val c = (gis.flatMap itemW).length by simp [σ1, Function.update_apply, hcL]]
        omega)
  have h4 := wclear_spec cap Lr gis.length ((σ1.seth i (σ1.sh i + 1)).setv c 0)
    (by simp [σ1, Function.update_apply, Ne.symm hcL]) (by simp [σ1, Function.update_apply, Ne.symm hcL]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ le_rfl
  apply WState.eq
  · funext j; by_cases hj : j = i
    · subst hj; simp [σ1, gisWord_eq]; omega
    · simp [σ1, Function.update_apply, hj]
  · rfl
  · funext q; by_cases hq : q = Lr
    · subst hq; simp [σ1, Function.update_apply, hL0]
    · by_cases hq2 : q = c
      · subst hq2; simp [σ1, Function.update_apply, hq, hc0]
      · simp [σ1, Function.update_apply, hq, hq2]
  · rfl

end NearCubicWires.WireExponent3_5.UnionMachine.RadCnt
