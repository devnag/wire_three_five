import Proof.Wire_3_5.Primitive.SeedFix.W6O

/-! # W6, part 16: the search's entry bank and the modulus read back

P3:2121-2157 (filt:majorant: the field `GF(2^{ℓ₀})`, its modulus `p` "the first primitive polynomial of degree `ℓ₀`",
`Majorant.refMod`): the entry bank `srIn ℓ₀` of C1's verified search on the streams `srT` (`W6O`'s words) and
the modulus read back from its answer tape into `rPM = 66` (`readFW`, then `+ 2^{ℓ₀}`):
* `srSt` (the fifteen words on `srT`), `srSt_srIn`, **`srPrep_exec`**;
* **`pm_exec`**: `r66 := (x mod 2^ℓ) + 2^ℓ` from `frame (binary ℓ x)` on `sMod`.

Paper quantities of the main types: the search's entry bank (degree `ℓ₀`) and the modulus value. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (cap : ℕ)

/-! ## The entry bank -/

/-- The fifteen entry words on `srT`. -/
def srSt (σ1 : WL) (ℓ : ℕ) : WL :=
  (((((((((((((((σ1).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 163 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 164 ([true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false])).sets 165 ([] ++ FiltRec.reps ℓ [true, true] ++ [false])).sets 166 ([false])).sets 167 ([false])).sets 168 ([false])).sets 169 ([false])).sets 170 ([false])).sets 171 ([] ++ FiltRec.reps ℓ [false, false] ++ [false, false])).sets 21 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 173 ([false])).sets 174 ([false])).sets 175 ([false])

theorem srSt_st0 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 161 = [] ++ FiltRec.reps ℓ [true, false] ++ [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st1 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 162 = [] ++ FiltRec.reps ℓ [true, false] ++ [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st2 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 163 = [] ++ FiltRec.reps ℓ [true, false] ++ [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st3 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 164 = [true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st4 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 165 = [] ++ FiltRec.reps ℓ [true, true] ++ [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st5 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 166 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st6 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 167 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st7 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 168 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st8 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 169 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st9 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 170 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st10 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 171 = [] ++ FiltRec.reps ℓ [false, false] ++ [false, false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st11 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 21 = [] ++ FiltRec.reps ℓ [true, false] ++ [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st12 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 173 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st13 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 174 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_st14 (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).st 175 = [false] := by
  unfold srSt
  simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]

theorem srSt_srIn (σ1 : WL) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (j : Fin 15) :
    (srSt σ1 ℓ).st (srT j) = GF2.srIn ℓ (2 * ℓ + 2) J00 0 0 false false false j := by
  fin_cases j
  · show (srSt σ1 ℓ).st 161 = _
    rw [srSt_st0]
    simp [GF2.srIn, J00, binary_zero, frame_rep]
  · show (srSt σ1 ℓ).st 162 = _
    rw [srSt_st1]
    simp [GF2.srIn, J00, binary_zero, frame_rep]
  · show (srSt σ1 ℓ).st 163 = _
    rw [srSt_st2]
    simp [GF2.srIn, J00, binary_zero, frame_rep]
  · show (srSt σ1 ℓ).st 164 = _
    rw [srSt_st3]
    simp [GF2.srIn, J00, frame_one ℓ h1]
  · show (srSt σ1 ℓ).st 165 = _
    rw [srSt_st4]
    simp [GF2.srIn, J00, binary_max, frame_rep]
  · show (srSt σ1 ℓ).st 166 = _
    rw [srSt_st5]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 167 = _
    rw [srSt_st6]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 168 = _
    rw [srSt_st7]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 169 = _
    rw [srSt_st8]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 170 = _
    rw [srSt_st9]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 171 = _
    rw [srSt_st10]
    simp [GF2.srIn, J00, zeros_rep]
  · show (srSt σ1 ℓ).st 21 = _
    rw [srSt_st11]
    simp [GF2.srIn, J00, binary_zero, frame_rep]
  · show (srSt σ1 ℓ).st 173 = _
    rw [srSt_st12]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 174 = _
    rw [srSt_st13]
    simp [GF2.srIn, J00]
  · show (srSt σ1 ℓ).st 175 = _
    rw [srSt_st14]
    simp [GF2.srIn, J00]

theorem srSt_other (σ1 : WL) (ℓ : ℕ) (s : Fin 192) (h : ∀ j, srT j ≠ s) : (srSt σ1 ℓ).st s = σ1.st s := by
  have n161 : s ≠ 161 := fun e => h 0 e.symm
  have n162 : s ≠ 162 := fun e => h 1 e.symm
  have n163 : s ≠ 163 := fun e => h 2 e.symm
  have n164 : s ≠ 164 := fun e => h 3 e.symm
  have n165 : s ≠ 165 := fun e => h 4 e.symm
  have n166 : s ≠ 166 := fun e => h 5 e.symm
  have n167 : s ≠ 167 := fun e => h 6 e.symm
  have n168 : s ≠ 168 := fun e => h 7 e.symm
  have n169 : s ≠ 169 := fun e => h 8 e.symm
  have n170 : s ≠ 170 := fun e => h 9 e.symm
  have n171 : s ≠ 171 := fun e => h 10 e.symm
  have n21 : s ≠ 21 := fun e => h 11 e.symm
  have n173 : s ≠ 173 := fun e => h 12 e.symm
  have n174 : s ≠ 174 := fun e => h 13 e.symm
  have n175 : s ≠ 175 := fun e => h 14 e.symm
  unfold srSt
  simp only [WState.sets_st, Function.update_apply, n161, n162, n163, n164, n165, n166, n167, n168, n169, n170, n171, n21, n173, n174, n175, if_false]

theorem prepABC_exec (σ1 : WL) (ℓ : ℕ) (g65 : σ1.val 65 = ℓ) (g75 : σ1.val 75 = ℓ - 1) (gop : σ1.val qOP = 0)
    (g77 : σ1.val 77 = 0) (g78 : σ1.val 78 = 0) (hs : ∀ j, σ1.st (srT j) = [] ∧ σ1.sh (srT j) = 0) (hb : 2 * ℓ + 4 ≤ cap) :
    WExec cap (.seq prepA (.seq prepB prepC)) σ1 (srSt σ1 ℓ) (16 * (4 * (opU cap + 1) + 1)) := by
  have eA := prepA_exec cap σ1 ℓ g65 g75 gop g77 g78 ⟨(hs 0).1, (hs 0).2⟩ ⟨(hs 1).1, (hs 1).2⟩ ⟨(hs 2).1, (hs 2).2⟩ ⟨(hs 3).1, (hs 3).2⟩ ⟨(hs 4).1, (hs 4).2⟩ hb
  have eB := prepB_exec cap ((((((σ1).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 163 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 164 ([true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false])).sets 165 ([] ++ FiltRec.reps ℓ [true, true] ++ [false])) ℓ g65 g75 gop g77 g78 ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 5).1, (hs 5).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 6).1, (hs 6).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 7).1, (hs 7).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 8).1, (hs 8).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 9).1, (hs 9).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 10).1, (hs 10).2⟩ hb
  have eC := prepC_exec cap ((((((((((((σ1).sets 161 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 162 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 163 ([] ++ FiltRec.reps ℓ [true, false] ++ [false])).sets 164 ([true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false])).sets 165 ([] ++ FiltRec.reps ℓ [true, true] ++ [false])).sets 166 ([false])).sets 167 ([false])).sets 168 ([false])).sets 169 ([false])).sets 170 ([false])).sets 171 ([] ++ FiltRec.reps ℓ [false, false] ++ [false, false])) ℓ g65 g75 gop g77 g78 ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 11).1, (hs 11).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 12).1, (hs 12).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 13).1, (hs 13).2⟩ ⟨by simp only [WState.sets_st, WState.sets_sh, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact (hs 14).1, (hs 14).2⟩ hb
  exact WExec.mono (WExec.seq eA (WExec.seq eB eC)) (by omega)

theorem srSt_st_congr (σ1 σ2 : WL) (ℓ : ℕ) (h : σ1.st = σ2.st) : (srSt σ1 ℓ).st = (srSt σ2 ℓ).st := by
  unfold srSt
  simp only [WState.sets_st, h]

def srPrep : WP :=
  .seq (wcopyR 65 75 76) (.seq (.dec 75) (.seq (.seq prepA (.seq prepB prepC)) (WM.clear 75)))

theorem srSt_sh (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).sh = σ1.sh := by unfold srSt; simp only [WState.sets_sh]
theorem srSt_val (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).val = σ1.val := by unfold srSt; simp only [WState.sets_val]
theorem srSt_cell (σ1 : WL) (ℓ : ℕ) : (srSt σ1 ℓ).cell = σ1.cell := by unfold srSt; rfl

theorem srPrep_core (σ1 : WL) (ℓ : ℕ) (g65 : σ1.val 65 = ℓ) (g75 : σ1.val 75 = ℓ - 1) (gop : σ1.val qOP = 0)
    (g77 : σ1.val 77 = 0) (g78 : σ1.val 78 = 0) (hs : ∀ j, σ1.st (srT j) = [] ∧ σ1.sh (srT j) = 0) (hb : 2 * ℓ + 4 ≤ cap) :
    WExec cap (.seq (.seq prepA (.seq prepB prepC)) (WM.clear 75)) σ1
      ⟨σ1.sh, (srSt σ1 ℓ).st, Function.update σ1.val 75 0, σ1.cell⟩ (17 * (4 * (opU cap + 1) + 1)) := by
  have hU := lin_le_opU cap
  have eP := prepABC_exec cap σ1 ℓ g65 g75 gop g77 g78 hs hb
  have r3 := clear_rr cap 75 σ1.val (by rw [g75]; omega) (srSt σ1 ℓ) (srSt_val σ1 ℓ)
  rw [srSt_sh, srSt_cell] at r3
  exact WExec.mono (WExec.seq eP r3) (by omega)

theorem srPrep_exec (σ : WL) (ℓ : ℕ) (h65 : σ.val 65 = ℓ) (h1 : 1 ≤ ℓ) (z75 : σ.val 75 = 0) (z76 : σ.val 76 = 0)
    (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (hop : σ.val qOP = 0)
    (hs : ∀ j, σ.st (srT j) = [] ∧ σ.sh (srT j) = 0) (hb : 2 * ℓ + 4 ≤ cap) :
    WExec cap srPrep σ ⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ (20 * (4 * (opU cap + 1) + 1)) := by
  have hU := lin_le_opU cap
  have hq75 : (75 : Fin 80) ≠ qOP := by decide
  have r1 := (wcopy_rr cap 65 75 76 (by decide) (by decide) (by decide) σ.val ℓ h65 z75 z76 (by omega)) σ rfl
  have r2 := (dec_rr cap 75 (Function.update σ.val 75 ℓ) (ℓ - 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega))
    ⟨σ.sh, σ.st, Function.update σ.val 75 ℓ, σ.cell⟩ rfl
  have g65 : Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1) 65 = ℓ := by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact h65
  have g75 : Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1) 75 = ℓ - 1 := by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
  have gop : Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1) qOP = 0 := by
    rw [Function.update_of_ne hq75.symm, Function.update_of_ne hq75.symm]; exact hop
  have g77 : Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1) 77 = 0 := by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z77
  have g78 : Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1) 78 = 0 := by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z78
  have eP := srPrep_core cap ⟨σ.sh, σ.st, Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1), σ.cell⟩ ℓ
    g65 g75 gop g77 g78 hs hb
  have hv : Function.update (Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1)) 75 0 = σ.val := by
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
    split_ifs with h
    · subst h; exact z75.symm
    · rfl
  have hst : (srSt ⟨σ.sh, σ.st, Function.update (Function.update σ.val 75 ℓ) 75 (ℓ - 1), σ.cell⟩ ℓ).st = (srSt σ ℓ).st :=
    srSt_st_congr _ σ ℓ rfl
  rw [hv, hst] at eP
  exact WExec.mono (WExec.seq r1 (WExec.seq r2 eP)) (by omega)

/-! ## The modulus read back -/

def Rp2 : Fin 4 ↪ Fin 80 := ⟨![65, 79, 77, 78], by decide⟩

/-- `r66 := (x mod 2^ℓ) + 2^ℓ` from `frame (binary ℓ x)` on `sMod` (`r65 = ℓ`). -/
def pmW : WP :=
  .seq (wcopyR 65 79 77) (.seq (readFW sMod 79 66 77 78) (.seq (UnaryArith.pow2W Rp2)
    (.seq (ParseNat.addTo 79 66 77) (WM.clear 79))))

theorem pm_exec (σ : WL) (ℓ x : ℕ) (h65 : σ.val 65 = ℓ) (hst : σ.st sMod = frame (binary ℓ x)) (hsh : σ.sh sMod = 0)
    (z66 : σ.val 66 = 0) (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (z79 : σ.val 79 = 0)
    (hb : 2 ^ (ℓ + 1) + ℓ + 2 ≤ cap) :
    WExec cap pmW σ ⟨Function.update σ.sh sMod (2 * ℓ), σ.st, Function.update σ.val 66 (x % 2 ^ ℓ + 2 ^ ℓ), σ.cell⟩
      (opU cap + 2 * (ℓ + 2) * (40 * 2 ^ ℓ + 40)) := by
  have hU := lin_le_opU cap
  have hxm : x % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ Nat.one_le_two_pow
  have hp2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have a1 := (wcopy_rr cap 65 79 77 (by decide) (by decide) (by decide) σ.val ℓ h65 z79 z77 (by omega)) σ rfl
  have a2 := readFW_spec cap sMod (79 : Fin 80) 66 77 78 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL) (binary ℓ x)
    (by show Function.update σ.val 79 ℓ 79 = _; rw [binary_length]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (by show Function.update σ.val 79 ℓ 77 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z77)
    (by show Function.update σ.val 79 ℓ 78 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z78)
    (fun m hm => by
      show readTapeBit (σ.st sMod) (σ.sh sMod + 2 * m + 1) = _
      rw [hst, hsh, frame_marks', Nat.zero_add]
      exact ParseNat.read_marks_bit [false] (binary ℓ x) m hm)
    (by show Function.update σ.val 79 ℓ 66 + 2 ^ ((binary ℓ x).length + 1) ≤ cap
        rw [binary_length]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rw [z66]; omega)
  rw [binary_length, bitsValue_binary'] at a2
  have v66 : Function.update σ.val 79 ℓ 66 = 0 := by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z66
  rw [show (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL).val 66 = 0 from v66, Nat.zero_add] at a2
  have a3 : WExec cap (UnaryArith.pow2W Rp2)
      (((WState.seth (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL) sMod (σ.sh sMod + 2 * ℓ)).setv 66
        (x % 2 ^ ℓ)).setv 79 0)
      ((((WState.seth (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL) sMod (σ.sh sMod + 2 * ℓ)).setv 66
        (x % 2 ^ ℓ)).setv 79 0).setv 79 (2 ^ ℓ)) (ℓ * (18 * 2 ^ ℓ + 7) + 18 * ℓ + 20) := by
    have h := UnaryArith.pow2W_spec cap Rp2 (((WState.seth (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL) sMod
      (σ.sh sMod + 2 * ℓ)).setv 66 (x % 2 ^ ℓ)).setv 79 0)
      (by show Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0 79 = 0; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
      (by show Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0 77 = 0
          simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z77)
      (by show Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0 78 = 0
          simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z78)
      (by show 2 ^ (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0 65 + 1) ≤ cap
          simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rw [h65]; omega)
    have e0 : Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0 65 = ℓ := by
      simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact h65
    exact e0 ▸ h
  have a4 := ParseNat.addTo_spec cap (79 : Fin 80) 66 77 (by decide) (by decide) (by decide)
    ((((WState.seth (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL) sMod (σ.sh sMod + 2 * ℓ)).setv 66
        (x % 2 ^ ℓ)).setv 79 0).setv 79 (2 ^ ℓ))
    (by show Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ) 77 = 0
        simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact z77)
    (by show Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ) 79 ≤ cap
        simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
    (by show Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ) 66 +
          Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ) 79 ≤ cap
        simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have e66 : Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ) 66 = x % 2 ^ ℓ := by
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
  have e79 : Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66 (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ) 79 = 2 ^ ℓ := by
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
  simp only [WState.setv_val, WState.seth_val] at a4
  rw [e66, e79] at a4
  have a5 := wclear_spec cap (79 : Fin 80) (2 ^ ℓ)
    (((((WState.seth (⟨σ.sh, σ.st, Function.update σ.val 79 ℓ, σ.cell⟩ : WL) sMod (σ.sh sMod + 2 * ℓ)).setv 66
        (x % 2 ^ ℓ)).setv 79 0).setv 79 (2 ^ ℓ)).setv 66 (x % 2 ^ ℓ + 2 ^ ℓ))
    (by simp only [WState.setv_val, WState.seth_val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (by simp only [WState.setv_val, WState.seth_val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  have k1 : ℓ * (36 * 2 ^ ℓ + 12 + 4) + ℓ * (18 * 2 ^ ℓ + 7) + 24 * 2 ^ ℓ + 18 * ℓ + 60 ≤ 2 * (ℓ + 2) * (40 * 2 ^ ℓ + 40) := by
    have := Nat.one_le_two_pow (n := ℓ)
    nlinarith [Nat.zero_le (ℓ * 2 ^ ℓ)]
  have hv : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update σ.val 79 ℓ) 66
      (x % 2 ^ ℓ)) 79 0) 79 (2 ^ ℓ)) 66 (x % 2 ^ ℓ + 2 ^ ℓ)) 79 0 = Function.update σ.val 66 (x % 2 ^ ℓ + 2 ^ ℓ) := by
    clear * - z79
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
    split_ifs <;> subst_vars <;> simp_all
  refine WExec.cast cap (WExec.seq a1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4 a5)))) ?_ (by omega)
  apply WState.eq
  · show Function.update σ.sh sMod (σ.sh sMod + 2 * ℓ) = Function.update σ.sh sMod (2 * ℓ)
    rw [hsh, Nat.zero_add]
  · rfl
  · exact hv
  · rfl

end NearCubicWires.WireExponent3_5.PrimT.W6
