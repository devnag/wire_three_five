import Proof.Wire_3_5.FinalPass.DigsPass2

/-! # `DigsW`'s body, part 12: the `τ₀` digits (P3:2596-2599)

`digitsW` = `digitW` run `τ₀` times, `R 35` counted down, `R 36 = d` counted up. After digits `0 … k − 1` the
output is `Wd l k = l ++ (range k).flatMap dWord`. Main declarations: `Wd`, `Wd_mono`, **`digits_spec`**. Paper
quantity: the word of all digit populations `v_{·,d}`, `d < τ₀`, of row `(g, p)`. -/

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

/-- The output after digits `0 … k − 1`. -/
def Wd (a' off bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool) (k : ℕ) : List Bool :=
  l ++ (List.range k).flatMap (dWord a' off bm p S ws)

theorem Wd_succ (a' off bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool) (k : ℕ) :
    Wd a' off bm p S ws l (k + 1) = Wd a' off bm p S ws l k ++ dWord a' off bm p S ws k := by
  simp [Wd, List.range_succ, List.flatMap_append]

theorem Wd_mono (a' off bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool) (k : ℕ) :
    ∀ j, k ≤ j → (Wd a' off bm p S ws l k).length ≤ (Wd a' off bm p S ws l j).length
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge k (j + 1) with h' | h'
    · have := Wd_mono a' off bm p S ws l k j (by omega); rw [Wd_succ]; simp; omega
    · rw [show k = j + 1 by omega]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The `τ₀` digits. -/
def digitsW (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) : WM ns nr := countW (R 35) (digitW R Pay Dg)

/-- The digit loop's state. -/
def digSt (σ : WState ns nr) (Dg : Fin (ns + 1)) (τ : ℕ) (W : List Bool) (k : ℕ) : WState ns nr :=
  outAt ((σ.setv (R 35) (τ - k)).setv (R 36) k) Dg (R 34) W

theorem digits_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (rest : ℕ → List Bool) (G p bm off τ U : ℕ)
    (l : List Bool) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p) (hbm : bm < p)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm)
    (hov : σ.val (R 4) = off) (hz : Zs R σ dL)
    (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hpU : p ≤ U) (hτU : τ ≤ U) (hlU : (Wd a' off bm p S ws l τ).length + off + Os S a' + 2 ≤ U)
    (haU : a' ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (digitsW R Pay Dg) (digSt R σ Dg τ (Wd a' off bm p S ws l 0) 0)
      (digSt R σ Dg τ (Wd a' off bm p S ws l τ) τ) (τ * (dB U + 4) + 1) := by
  have hF := count_spec cap (R 35) (digitW R Pay Dg) τ (dB U) (by omega)
    (fun k => digSt R σ Dg τ (Wd a' off bm p S ws l k) k) (fun k _ => by simp [digSt, outAt])
    (fun k hk => by
      have hW := Wd_mono a' off bm p S ws l (k + 1) τ hk
      rw [Wd_succ] at hW
      have hLs : Ls off k bm p S ws (Wd a' off bm p S ws l k) a' ++ [false] = Wd a' off bm p S ws l (k + 1) := by
        rw [Wd_succ, Ls_prefix, dWord, List.append_assoc]
      have dx := digit_spec cap R Pay Dg hPD a' ha cD S m zs ws rest G p bm k off U (Wd a' off bm p S ws l k)
        ((digSt R σ Dg τ (Wd a' off bm p S ws l k) k).setv (R 35) (τ - k - 1))
        (fun i hi => by simp [digSt, outAt, Function.update_apply, hPD i, hst i hi])
        (fun i hi => by simp [digSt, outAt, Function.update_apply, hPD i, hs i hi]) hc hzs hws hm hGa hp hbm
        (by simp [digSt, outAt]) (by simp [digSt, outAt]) (by simp [digSt, outAt]) (by simp [digSt, outAt, hA])
        (by simp [digSt, outAt, hG]) (by simp [digSt, outAt, hP]) (by simp [digSt, outAt, h23])
        (by simp [digSt, outAt]) (by simp [digSt, outAt, hov])
        (fun r hr => by
          have r35 : r ≠ 35 := by rintro rfl; revert hr; decide
          have r36 : r ≠ 36 := by rintro rfl; revert hr; decide
          have r34 : r ≠ 34 := by rintro rfl; revert hr; decide
          have := hz r hr
          simp [digSt, outAt, Function.update_apply, R.injective.ne r35, R.injective.ne r36, R.injective.ne r34, this])
        hcU hmU hGU hpU (by omega)
        (by rw [Ls_prefix]; simp [dWord] at hW ⊢; omega) haU hU
      refine WExec.cast cap dx ?_ le_rfl
      rw [hLs]
      unfold digSt
      rw [show τ - (k + 1) = τ - k - 1 by omega]
      clear dx hz
      refine WState.eq ?_ ?_ ?_ ?_
      · wst_sh
      · wst_st
      · funext y
        by_cases y1 : y = R 35
        · rw [y1]; simp_all [outAt, Function.update_apply]
        by_cases y2 : y = R 36
        · rw [y2]; simp_all [outAt, Function.update_apply]
        by_cases y3 : y = R 34
        · rw [y3]; simp_all [outAt, Function.update_apply]
        simp_all [outAt, Function.update_apply]
      · rfl)
  exact hF

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
