import Proof.Wire_3_5.FinalPass.ThrPtRS20

/-! # S2 (THR per point), part 35: the evaluator's entry state (P3:3170-3178)

`Init0 σ₀ a G τ M`: the internal entry — every head at `0`, the cell `false`, the scratch streams empty, the
accumulator `0`, the call's numbers `a, |𝒢|, τ₀, |occs|` in registers `5, 109, 8, 63`, every other register `0`.
**`init_w`**: the entry is the working state `tInit G` over itself; **`baseOK_of`**: the base the rows run over (the
width in register `117`) meets `BaseOK`; **`rowReady_setup`**: the state the setup leaves is `RowReady`.
Paper quantity: none beyond the machine model (the per-point entry `PtIn2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- **The internal entry.** -/
structure Init0 (σ0 : WState 16 118) (a G τ M : ℕ) : Prop where
  sh : ∀ j, σ0.sh j = 0
  cell : σ0.cell = false
  s10 : σ0.st 10 = []
  s11 : σ0.st 11 = []
  s12 : σ0.st 12 = []
  s13 : σ0.st 13 = []
  s14 : σ0.st 14 = []
  s15 : σ0.st 15 = []
  s16 : σ0.st 16 = []
  v0 : σ0.val 0 = 0
  v5 : σ0.val 5 = a
  v8 : σ0.val 8 = τ
  v63 : σ0.val 63 = M
  v109 : σ0.val 109 = G
  zero : ∀ q : Fin 118, q.val ≠ 0 → q.val ≠ 5 → q.val ≠ 8 → q.val ≠ 63 → q.val ≠ 109 → σ0.val q = 0

theorem init_w (σ0 : WState 16 118) (a G τ M : ℕ) (I : Init0 σ0 a G τ M) : (tInit G).w σ0 = σ0 := by
  have z := I.zero
  apply WState.eq
  · funext j
    show tHd (tInit G) j (σ0.sh j) = σ0.sh j
    unfold tHd
    split_ifs <;> first | rfl | exact (I.sh j).symm
  · funext j
    show tStr (tInit G) j (σ0.st j) = σ0.st j
    unfold tStr
    split_ifs with h1 h2 h3 h4 h5 h6 h7
    · subst h1; exact I.s10.symm
    · subst h2; exact I.s11.symm
    · subst h3; exact I.s12.symm
    · subst h4; exact I.s13.symm
    · subst h5; exact I.s14.symm
    · subst h6; exact I.s15.symm
    · subst h7; exact I.s16.symm
    · rfl
  · funext q
    by_cases h0 : q.val = 0
    · obtain rfl : q = 0 := Fin.ext h0
      rw [tw_val_acc]; exact I.v0.symm
    by_cases h6 : q.val = 6
    · obtain rfl : q = 6 := Fin.ext h6
      rw [tw_val_gi]; exact (z 6 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h7 : q.val = 7
    · obtain rfl : q = 7 := Fin.ext h7
      rw [tw_val_p]; exact (z 7 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h53 : q.val = 53
    · obtain rfl : q = 53 := Fin.ext h53
      rw [tw_val_d]; exact (z 53 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h82 : q.val = 82
    · obtain rfl : q = 82 := Fin.ext h82
      rw [tw_val_r82]; exact (z 82 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h92 : q.val = 92
    · obtain rfl : q = 92 := Fin.ext h92
      rw [tw_val_w92]; exact (z 92 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h109 : q.val = 109
    · obtain rfl : q = 109 := Fin.ext h109
      rw [tw_val_gRem]; exact I.v109.symm
    by_cases h110 : q.val = 110
    · obtain rfl : q = 110 := Fin.ext h110
      rw [tw_val_prH]; exact (z 110 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h111 : q.val = 111
    · obtain rfl : q = 111 := Fin.ext h111
      rw [tw_val_dRem]; exact (z 111 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h112 : q.val = 112
    · obtain rfl : q = 112 := Fin.ext h112
      rw [tw_val_rH]; exact (z 112 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h113 : q.val = 113
    · obtain rfl : q = 113 := Fin.ext h113
      rw [tw_val_tmp]; exact (z 113 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h114 : q.val = 114
    · obtain rfl : q = 114 := Fin.ext h114
      rw [tw_val_kS]; exact (z 114 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h115 : q.val = 115
    · obtain rfl : q = 115 := Fin.ext h115
      rw [tw_val_rS]; exact (z 115 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    by_cases h116 : q.val = 116
    · obtain rfl : q = 116 := Fin.ext h116
      rw [tw_val_rwH]; exact (z 116 (by decide) (by decide) (by decide) (by decide) (by decide)).symm
    exact tw_val_other σ0 _ q h0 h6 h7 h53 h82 h92 h109 h110 h111 h112 h113 h114 h115 h116
  · exact I.cell.symm

theorem baseOK_of (σ0 : WState 16 118) (a G τ M : ℕ) (I : Init0 σ0 a G τ M) (H : ℕ) :
    BaseOK (σ0.setv 117 H) a τ M where
  sh := fun j => I.sh j
  vA := by rw [WState.setv_val, Function.update_of_ne (by decide)]; exact I.v5
  vT := by rw [WState.setv_val, Function.update_of_ne (by decide)]; exact I.v8
  vO := by
    rw [WState.setv_val, Function.update_of_ne (by decide)]
    exact I.zero 9 (by decide) (by decide) (by decide) (by decide) (by decide)
  rowZ := fun q h1 h2 => by
    rw [WState.setv_val, Function.update_of_ne (fun h => by subst h; simp at h2)]
    exact I.zero q (by omega) (by omega) (by omega) (by omega) (by omega)
  vM := by rw [WState.setv_val, Function.update_of_ne (by decide)]; exact I.v63
  popZ := fun q h1 h2 => by
    rw [WState.setv_val, Function.update_of_ne (fun h => by subst h; simp at h2)]
    exact I.zero q (by omega) (by omega) (by omega) (by omega) (by omega)
  stZ := fun q h1 h2 => by
    rw [WState.setv_val, Function.update_of_ne (fun h => by subst h; simp at h2)]
    exact I.zero q (by omega) (by omega) (by omega) (by omega) (by omega)
  cell := I.cell

theorem rowReady_setup (G τ M : ℕ) (P N : List Bool) (X : List Bool) :
    RowReady { tInit G with
      dRem := τ, kS := M, pos := P, neg := N, x := frameP X ++ [false],
      z := List.replicate (2 * M + 1) false } M τ X where
  rw := fun b hb => by simp [tInit] at hb
  hRw := rfl
  rwH := rfl
  z := ⟨List.replicate (2 * M) false, List.replicate_succ' .., by simp⟩
  ss := fun b hb => by simp [tInit] at hb
  rep := fun b hb => by simp [tInit] at hb
  hRep := rfl
  rH := rfl
  d := rfl
  dRem := rfl
  kS := rfl
  rS := rfl
  r82 := rfl
  w92 := rfl
  x := rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
