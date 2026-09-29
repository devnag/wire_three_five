import Proof.Wire_3_5.FinalPass.S5TWin1

/-! # S5-THR, part 14: stage 4's input word from W6's ports (P3:2150-2157, 2220-2231)

Stage 4's table builder (`Hash4.build_spec`) reads `winWord M L J W = unary M ++ unary L ++ unary J ++ winRecs ++
[false]` at `L = M = |occs|`. W6 leaves `1^M` (port 9), `1^J` (port 12) and the level records `winRecs` (port 18).

* `wSt` (the written state), `cSt_wSt`, `cSt_rew`, `fieldR` / **`fieldR_spec`** (a unary field copied, the port
  rewound), `recsR` / **`recsR_spec`**, `emitK_wSt`, `recsCost_le`;
* `winW` / **`winW_spec`**: the four fields and the closing `0` on a blank stream `WIN`, every head back at `0`,
  the counters at `0`; **`winW_hash`**: the same at `Hash4.winWord M M J W` (`flatMap_winRec`).

Paper quantity of the main type: stage 4's input word `winWord M M J W` (the levels' moduli and windows). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-- The written state: `u` appended to `O`, counted in `KW`. -/
def wSt (O : Fin (ns + 1)) (KW : Fin nr) (σ : WState ns nr) (u : List Bool) : WState ns nr :=
  (appW σ O u).setv KW (σ.val KW + u.length)

section Copy
variable {P O : Fin (ns + 1)} {K KW : Fin nr}

theorem cSt_wSt (hPO : P ≠ O) (hK : K ≠ KW) (σ : WState ns nr) (hK0 : σ.val K = 0) (u : List Bool) :
    cSt P O K KW σ u 0 = wSt O KW σ u := by
  apply WState.eq
  · funext i
    by_cases hi : i = P
    · subst hi; simp [cSt, wSt, Function.update_apply, hPO]
    · simp [cSt, wSt, Function.update_apply, hi]
  · rfl
  · funext r
    by_cases hr : r = K
    · subst hr; simp [cSt, wSt, Function.update_apply, hK, hK0]
    · simp [cSt, wSt, Function.update_apply, hr]
  · rfl

theorem cSt_rew (hPO : P ≠ O) (σ : WState ns nr) (hK0 : σ.val K = 0) (u : List Bool) (d : ℕ) (hK : K ≠ KW) :
    ((cSt P O K KW σ u d).setv K 0).seth P ((cSt P O K KW σ u d).sh P - d) = cSt P O K KW σ u 0 := by
  apply WState.eq
  · funext i
    by_cases hi : i = P
    · subst hi; simp [cSt_sh]
    · simp only [WState.seth_sh, WState.setv_sh, Function.update_apply, hi, if_false, cSt_sh]
  · rfl
  · funext r
    by_cases hr : r = K
    · subst hr; simp [cSt_val, hK, hK0]
    · simp only [WState.seth_val, WState.setv_val, Function.update_apply, hr, if_false, cSt_val]
  · rfl

end Copy

/-- A unary field copied, the port rewound. -/
def fieldR (P O : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr := .seq (fieldK P O K KW) (WM.rewind P K)

theorem fieldR_spec (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (hK0 : σ.val K = 0) (a : ℕ) (u : List Bool)
    (hones : ∀ i < a, readTapeBit (σ.st P) (σ.sh P + i) = true) (hend : readTapeBit (σ.st P) (σ.sh P + a) = false)
    (hc : σ.val KW + u.length + a + 1 ≤ cap) :
    WExec cap (fieldR P O K KW) (wSt O KW σ u) (wSt O KW σ (u ++ (List.replicate a true ++ [false]))) (20 * a + 22) := by
  have e1 := fieldK_spec cap P O hPO K KW hK σ a u 0 (by simpa using hones) (by simpa using hend)
    (by rw [hK0]; omega) hc
  rw [cSt_wSt hPO hK σ hK0] at e1
  have e2 := wrewind_spec cap P K (0 + a + 1) (cSt P O K KW σ (u ++ (List.replicate a true ++ [false])) (0 + a + 1))
    (by rw [cSt_val, if_neg hK, if_pos rfl, hK0]; omega) (by rw [cSt_val, if_neg hK, if_pos rfl, hK0]; omega)
  rw [cSt_rew hPO σ hK0 _ _ hK, cSt_wSt hPO hK σ hK0] at e2
  exact WExec.cast cap (WExec.seq e1 e2) rfl (by omega)

/-- The records copied, the port rewound. -/
def recsR (P O : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr := .seq (recsK P O K KW) (WM.rewind P K)

theorem recsCost_le : ∀ rs : List (ℕ × ℕ), recsCost rs ≤ 16 * (recsW rs).length + 1
  | [] => by simp [recsCost]
  | (a, b) :: rs => by
    have ih := recsCost_le rs
    have hl : (recsW ((a, b) :: rs)).length = (a + b + 3) + (recsW rs).length := by
      rw [show recsW ((a, b) :: rs) = recW (a, b) ++ recsW rs from rfl, List.length_append, recW_length]
    rw [hl]; simp only [recsCost]; omega

theorem recsR_spec (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (hK0 : σ.val K = 0) (rs : List (ℕ × ℕ)) (u : List Bool) (hd : (σ.st P).drop (σ.sh P) = recsW rs)
    (hc : σ.val KW + u.length + (recsW rs).length ≤ cap) :
    WExec cap (recsR P O K KW) (wSt O KW σ u) (wSt O KW σ (u ++ recsW rs)) (21 * (recsW rs).length + 3) := by
  have e1 := recsK_spec cap P O hPO K KW hK σ [] rfl rs u 0 (by simpa using hd) (by rw [hK0]; omega) hc
  rw [cSt_wSt hPO hK σ hK0] at e1
  have e2 := wrewind_spec cap P K (0 + (recsW rs).length) (cSt P O K KW σ (u ++ recsW rs) (0 + (recsW rs).length))
    (by rw [cSt_val, if_neg hK, if_pos rfl, hK0]; omega) (by rw [cSt_val, if_neg hK, if_pos rfl, hK0]; omega)
  rw [cSt_rew hPO σ hK0 _ _ hK, cSt_wSt hPO hK σ hK0] at e2
  have := recsCost_le rs
  exact WExec.cast cap (WExec.seq e1 e2) rfl (by omega)

theorem emitK_wSt (P O : Fin (ns + 1)) (hPO : P ≠ O) (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr)
    (hK0 : σ.val K = 0) (u : List Bool) (b : Bool) (hc : σ.val KW + u.length < cap) :
    WExec cap (emitK O KW b) (wSt O KW σ u) (wSt O KW σ (u ++ [b])) 7 := by
  have e := emitK_cSt cap hPO hK σ u 0 b hc
  rwa [cSt_wSt hPO hK σ hK0, cSt_wSt hPO hK σ hK0] at e

theorem reads_ones (l : List Bool) (a : ℕ) (hl : l = List.replicate a true) :
    (∀ i < a, readTapeBit l (0 + i) = true) ∧ readTapeBit l (0 + a) = false := by
  subst hl
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [rd_drop]; simp [List.getD_eq_getElem?_getD, hi]
  · rw [rd_drop]; simp [List.getD_eq_getElem?_getD]

/-- **Stage 4's input word**: `M`, `M`, `J` and the records copied, then the closing `0`, `WIN` rewound. -/
def winW (P9 P12 P18 WIN : Fin (ns + 1)) (K KW : Fin nr) : WM ns nr :=
  .seq (fieldR P9 WIN K KW) (.seq (fieldR P9 WIN K KW) (.seq (fieldR P12 WIN K KW) (.seq (recsR P18 WIN K KW)
    (.seq (emitK WIN KW false) (WM.rewind WIN KW)))))

/-- The word `winW` writes. -/
def winU (M J : ℕ) (rs : List (ℕ × ℕ)) : List Bool :=
  (List.replicate M true ++ [false]) ++ (List.replicate M true ++ [false]) ++ (List.replicate J true ++ [false]) ++
    recsW rs ++ [false]

theorem winW_spec (P9 P12 P18 WIN : Fin (ns + 1)) (h9 : P9 ≠ WIN) (h12 : P12 ≠ WIN) (h18 : P18 ≠ WIN)
    (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr) (M J : ℕ) (rs : List (ℕ × ℕ))
    (hP9 : σ.st P9 = List.replicate M true) (hP9h : σ.sh P9 = 0)
    (hP12 : σ.st P12 = List.replicate J true) (hP12h : σ.sh P12 = 0)
    (hP18 : σ.st P18 = recsW rs) (hP18h : σ.sh P18 = 0) (hW : σ.st WIN = []) (hWh : σ.sh WIN = 0)
    (hK0 : σ.val K = 0) (hKW : σ.val KW = 0) (hcap : (winU M J rs).length ≤ cap) :
    WExec cap (winW P9 P12 P18 WIN K KW) σ (σ.sets WIN (winU M J rs)) (30 * (winU M J rs).length + 100) := by
  have hlen : (winU M J rs).length = (M + 1) + (M + 1) + (J + 1) + (recsW rs).length + 1 := by
    simp [winU]; omega
  have w0 : wSt WIN KW σ [] = σ := by
    unfold wSt; rw [appW_nil σ WIN (by rw [hW, hWh]; rfl), List.length_nil, Nat.add_zero, wsetv_same]
  obtain ⟨o9, e9⟩ := reads_ones (σ.st P9) M hP9
  obtain ⟨o12, e12⟩ := reads_ones (σ.st P12) J hP12
  have s1 := fieldR_spec cap P9 WIN h9 K KW hK σ hK0 M [] (by rw [hP9h]; exact o9) (by rw [hP9h]; exact e9)
    (by rw [hKW]; simp; omega)
  have s2 := fieldR_spec cap P9 WIN h9 K KW hK σ hK0 M ([] ++ (List.replicate M true ++ [false]))
    (by rw [hP9h]; exact o9) (by rw [hP9h]; exact e9) (by rw [hKW]; simp; omega)
  have s3 := fieldR_spec cap P12 WIN h12 K KW hK σ hK0 J
    ([] ++ (List.replicate M true ++ [false]) ++ (List.replicate M true ++ [false]))
    (by rw [hP12h]; exact o12) (by rw [hP12h]; exact e12) (by rw [hKW]; simp; omega)
  have s4 := recsR_spec cap P18 WIN h18 K KW hK σ hK0 rs
    ([] ++ (List.replicate M true ++ [false]) ++ (List.replicate M true ++ [false]) ++
      (List.replicate J true ++ [false])) (by rw [hP18, hP18h]; rfl) (by rw [hKW]; simp; omega)
  have s5 := emitK_wSt cap P18 WIN h18 K KW hK σ hK0
    ([] ++ (List.replicate M true ++ [false]) ++ (List.replicate M true ++ [false]) ++
      (List.replicate J true ++ [false]) ++ recsW rs) false (by rw [hKW]; simp; omega)
  have hu : [] ++ (List.replicate M true ++ [false]) ++ (List.replicate M true ++ [false]) ++
      (List.replicate J true ++ [false]) ++ recsW rs ++ [false] = winU M J rs := by simp [winU]
  rw [hu] at s5
  have s6 := wrewind_spec cap WIN KW (winU M J rs).length (wSt WIN KW σ (winU M J rs))
    (by simp [wSt, hKW]) (by simp [wSt, hKW]; omega)
  have hfin : ((wSt WIN KW σ (winU M J rs)).setv KW 0).seth WIN
      ((wSt WIN KW σ (winU M J rs)).sh WIN - (winU M J rs).length) = σ.sets WIN (winU M J rs) := by
    apply WState.eq
    · funext i
      by_cases hi : i = WIN
      · subst hi; simp [wSt, hW, hWh]
      · simp [wSt, Function.update_apply, hi]
    · funext i
      by_cases hi : i = WIN
      · subst hi; simp [wSt, hW]
      · simp [wSt, Function.update_apply, hi]
    · funext r
      by_cases hr : r = KW
      · subst hr; simp [wSt, hKW]
      · simp [wSt, Function.update_apply, hr]
    · rfl
  rw [hfin] at s6
  rw [w0] at s1
  have := recsCost_le rs
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) rfl ?_
  rw [hlen]; omega

/-- The level records as pairs. -/
theorem flatMap_winRec (J : ℕ) (W : ℕ → ℕ) :
    (ListEval.levels J).flatMap (Hash4.winRec J W) =
      recsW ((ListEval.levels J).map fun j => (ListEval.pow (ListEval.topW J W j), ListEval.topW J W j)) := by
  unfold recsW
  rw [List.flatMap_map]
  congr 1
  funext j
  simp [Hash4.winRec, recW, ListEval.unary]

theorem winU_hash (M J : ℕ) (W : ℕ → ℕ) :
    winU M J ((ListEval.levels J).map fun j => (ListEval.pow (ListEval.topW J W j), ListEval.topW J W j)) =
      Hash4.winWord M M J W := by
  unfold winU
  rw [← flatMap_winRec]
  simp [Hash4.winWord, ListEval.unary, List.append_assoc]

/-- **Stage 4's input word at the hash's levels.** -/
theorem winW_hash (P9 P12 P18 WIN : Fin (ns + 1)) (h9 : P9 ≠ WIN) (h12 : P12 ≠ WIN) (h18 : P18 ≠ WIN)
    (K KW : Fin nr) (hK : K ≠ KW) (σ : WState ns nr) (M J : ℕ) (W : ℕ → ℕ)
    (hP9 : σ.st P9 = List.replicate M true) (hP9h : σ.sh P9 = 0)
    (hP12 : σ.st P12 = List.replicate J true) (hP12h : σ.sh P12 = 0)
    (hP18 : σ.st P18 = (ListEval.levels J).flatMap (Hash4.winRec J W)) (hP18h : σ.sh P18 = 0)
    (hW : σ.st WIN = []) (hWh : σ.sh WIN = 0) (hK0 : σ.val K = 0) (hKW : σ.val KW = 0)
    (hcap : (Hash4.winWord M M J W).length ≤ cap) :
    WExec cap (winW P9 P12 P18 WIN K KW) σ (σ.sets WIN (Hash4.winWord M M J W))
      (30 * (Hash4.winWord M M J W).length + 100) := by
  rw [← winU_hash] at hcap ⊢
  exact winW_spec cap P9 P12 P18 WIN h9 h12 h18 K KW hK σ M J _ hP9 hP9h hP12 hP12h
    (by rw [hP18, flatMap_winRec]) hP18h hW hWh hK0 hKW hcap

end NearCubicWires.WireExponent3_5.FinalPass.S5T
