import Proof.Wire_3_5.FinalPass.DigsPass1

/-! # `DigsW`'s body, part 11: one digit, then all `τ₀` digits (P3:2596-2599)

`digitW` at digit `d`: `R 17 := g`, `R 25 := 1`, `R 38 := a'`, the circuits, the digit's closing `false`, `d += 1`,
`R 37`, `R 25` cleared. `digitsW` runs it `τ₀` times (`R 35` counted down). The output after digits `0 … k − 1` is
`Wd k = l ++ (range k).flatMap dWord`, `dWord d = Ls … [] a' ++ [false]`. Main declarations: `Ls_prefix`, `dWord`,
**`digit_spec`**, **`digits_spec`**. Paper quantity: the digit populations `v_{·,d}`, `d < τ₀`, of row `(g, p)` as
the word `digsWord`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

theorem Ls_prefix (off d bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool) :
    ∀ i, Ls off d bm p S ws l i = l ++ Ls off d bm p S ws [] i
  | 0 => by simp [Ls]
  | i + 1 => by rw [Ls, Ls, Ls_prefix off d bm p S ws l i, List.append_assoc]

/-- Digit `d`'s word: the circuits' emissions, then the closing `false`. -/
def dWord (a' off bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (d : ℕ) : List Bool :=
  Ls off d bm p S ws [] a' ++ [false]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- One digit. -/
def digitW (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (Hash4.wcopyR (R 1) (R 17) (R 39)) (.seq (.inc (R 25)) (.seq (Hash4.wcopyR (R 0) (R 38) (R 39))
    (.seq (circW (R 38) (fun i => cBodyDW R (Pay i) Dg)) (.seq (emitBitW Dg (R 34) false) (.seq (.inc (R 36))
    (.seq (WM.clear (R 37)) (WM.clear (R 25))))))))

/-- One digit's uniform bound. -/
def dB (U : ℕ) : ℕ :=
  18 * U + 3 + 1 + (3 + 1 + (18 * U + 3 + 1 + ((4 * (cDB U + 3) + 3) + 1 + (7 + 1 + (3 + 1 + (3 * U + 1 + 1 +
    (3 * U + 1)))))))

/-- A digit's zero registers. -/
def dL : List (Fin digsK) :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 27, 28, 29, 30, 31, 32, 33, 37, 38, 39,
    40]

theorem digit_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (rest : ℕ → List Bool) (G p bm d off U : ℕ)
    (l : List Bool) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p) (hbm : bm < p)
    (hlst : σ.st Dg = l) (hlsh : σ.sh Dg = l.length) (hlw : σ.val (R 34) = l.length)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm)
    (hdv : σ.val (R 36) = d) (hov : σ.val (R 4) = off) (hz : Zs R σ dL)
    (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hpU : p ≤ U) (hdU : d + 1 ≤ U) (hlU : (Ls off d bm p S ws l a').length + off + Os S a' + 2 ≤ U)
    (haU : a' ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (digitW R Pay Dg) σ (outAt (σ.setv (R 36) (d + 1)) Dg (R 34) (Ls off d bm p S ws l a' ++ [false]))
      (dB U) := by
  have h17 := hz 17 (by decide)
  have h25 := hz 25 (by decide)
  have h37 := hz 37 (by decide)
  have h38 := hz 38 (by decide)
  have h39 := hz 39 (by decide)
  have d1 := Hash4.wcopyR_spec cap (R 1) (R 17) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) σ h17 h39 (by omega)
  rw [hG] at d1
  have d2 := WExec.inc (cap := cap) (R 25) (σ.setv (R 17) G) (by simp [h25]; omega)
  rw [show (σ.setv (R 17) G).val (R 25) + 1 = 1 by simp [h25]] at d2
  have d3 := Hash4.wcopyR_spec cap (R 0) (R 38) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((σ.setv (R 17) G).setv (R 25) 1) (by simp [h38]) (by simp [h39])
    (by simp [hA]; omega)
  rw [show ((σ.setv (R 17) G).setv (R 25) 1).val (R 0) = a' by simp [hA]] at d3
  have e3 : ((σ.setv (R 17) G).setv (R 25) 1).setv (R 38) a' = circDSt R σ Dg a' G off d bm p S m ws l 0 := by
    unfold circDSt; clear d1 d2 d3 hz
    simp only [Gs, Bs, Os, Ls, Nat.sub_zero]
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y1 : y = R 17
      · rw [y1]; simp_all [outAt, Function.update_apply]
      by_cases y2 : y = R 25
      · rw [y2]; simp_all [outAt, Function.update_apply]
      by_cases y3 : y = R 37
      · rw [y3]; simp_all [outAt, Function.update_apply]
      by_cases y4 : y = R 38
      · rw [y4]; simp_all [outAt, Function.update_apply]
      by_cases y5 : y = R 34
      · rw [y5]; simp_all [outAt, Function.update_apply]
      simp_all [outAt, Function.update_apply]
    · rfl
  rw [e3] at d3
  have d4 := circD_spec cap R Pay Dg hPD a' ha cD S m zs ws rest G p bm d off U l σ hst hs hc hzs hws hm hp hbm hP h23
    hdv hov (Zs_sub R _ _ _ (by decide) hz) hcU hmU hGU hpU (by omega) hlU haU hU
  have d5 := emitBit_spec cap Dg (R 34) false (circDSt R σ Dg a' G off d bm p S m ws l a') (Ls off d bm p S ws l a')
    (by simp [circDSt]) (by simp [circDSt]) (by simp [circDSt]) (by omega)
  have d6 := WExec.inc (cap := cap) (R 36) (outAt (circDSt R σ Dg a' G off d bm p S m ws l a') Dg (R 34)
    (Ls off d bm p S ws l a' ++ [false])) (by simp [circDSt, outAt, hdv]; omega)
  have hBa := Bs_lt bm p hp a'
  have d7 := wclear_spec cap (R 37) (Os S a') ((outAt (circDSt R σ Dg a' G off d bm p S m ws l a') Dg (R 34)
    (Ls off d bm p S ws l a' ++ [false])).setv (R 36) ((outAt (circDSt R σ Dg a' G off d bm p S m ws l a') Dg (R 34)
    (Ls off d bm p S ws l a' ++ [false])).val (R 36) + 1)) (by simp [circDSt, outAt]) (by simp [circDSt, outAt]; omega)
  have d8 := wclear_spec cap (R 25) (Bs bm p a') (((outAt (circDSt R σ Dg a' G off d bm p S m ws l a') Dg (R 34)
    (Ls off d bm p S ws l a' ++ [false])).setv (R 36) ((outAt (circDSt R σ Dg a' G off d bm p S m ws l a') Dg (R 34)
    (Ls off d bm p S ws l a' ++ [false])).val (R 36) + 1)).setv (R 37) 0) (by simp [circDSt, outAt])
    (by simp [circDSt, outAt]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6
    (WExec.seq d7 d8))))))) ?_ (by unfold dB; omega)
  unfold circDSt
  clear d1 d2 d3 d4 d5 d6 d7 d8 e3 hz
  refine WState.eq ?_ ?_ ?_ ?_
  · wst_sh
  · wst_st
  · funext y
    by_cases y1 : y = R 17
    · rw [y1]; simp_all [outAt, Function.update_apply]
    by_cases y2 : y = R 25
    · rw [y2]; simp_all [outAt, Function.update_apply]
    by_cases y3 : y = R 37
    · rw [y3]; simp_all [outAt, Function.update_apply]
    by_cases y4 : y = R 38
    · rw [y4]; simp_all [outAt, Function.update_apply]
    by_cases y5 : y = R 34
    · rw [y5]; simp_all [outAt, Function.update_apply]
    by_cases y6 : y = R 36
    · rw [y6]; simp_all [outAt, Function.update_apply]
    simp_all [outAt, Function.update_apply]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
