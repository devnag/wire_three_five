import Proof.Wire_3_5.FinalPass.DigsCost1

/-! # `DigsW`'s body, part 10: the circuits at digit `d` (P3:2585-2599)

The circuit loop at digit `d` runs `cBodyDW` on payload `i` for `i < a'` (four guarded slots). Its state `circDSt i`:
`R 17 = Gs i = g / Π_{j<i} m_j`, `R 25 = Bs i = base^i mod p`, `R 37 = Os i = Σ_{j<i} |supp_j|`, `R 38 = a' − i`,
output `Ls i` (the prefix `l`, then circuit `j`'s `emitList` for `j < i`). Main declarations: `Gs`, `Bs`, `Os`, `Ls`,
`circDSt`, **`circD_spec`**. Paper quantity: digit `d`'s population word over circuits `0 … a' − 1`. -/

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

/-- The selection register before circuit `i`. -/
def Gs (G : ℕ) (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => G
  | i + 1 => Gs G m i / m i

/-- The power before circuit `i`: `base^i mod p` (with `bm = base mod p`). -/
def Bs (bm p : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => Bs bm p i * bm % p

/-- The occurrence offset before circuit `i`. -/
def Os (S : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => Os S i + S i

/-- The output before circuit `i` at digit `d`. -/
def Ls (off d bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool) : ℕ → List Bool
  | 0 => l
  | i + 1 => Ls off d bm p S ws l i ++ emitList off d (Bs bm p i) p (Os S i) (ws i)

theorem Bs_lt (bm p : ℕ) (hp : 2 ≤ p) : ∀ i, Bs bm p i < p
  | 0 => by simp [Bs]; omega
  | i + 1 => Nat.mod_lt _ (by omega)

theorem Gs_le (G : ℕ) (m : ℕ → ℕ) : ∀ i, Gs G m i ≤ G
  | 0 => le_rfl
  | i + 1 => le_trans (Nat.div_le_self _ _) (Gs_le G m i)

theorem Os_mono (S : ℕ → ℕ) (i : ℕ) : ∀ j, i ≤ j → Os S i ≤ Os S j
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := Os_mono S i j (by omega); simp [Os]; omega
    · rw [show i = j + 1 by omega]

theorem Ls_mono (off d bm p : ℕ) (S : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool) (i : ℕ) :
    ∀ j, i ≤ j → (Ls off d bm p S ws l i).length ≤ (Ls off d bm p S ws l j).length
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := Ls_mono off d bm p S ws l i j (by omega); simp [Ls]; omega
    · rw [show i = j + 1 by omega]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The circuit loop's state at digit `d`. -/
def circDSt (σ : WState ns nr) (Dg : Fin (ns + 1)) (a' G off d bm p : ℕ) (S m : ℕ → ℕ) (ws : ℕ → List ℤ)
    (l : List Bool) (i : ℕ) : WState ns nr :=
  outAt ((((σ.setv (R 17) (Gs G m i)).setv (R 25) (Bs bm p i)).setv (R 37) (Os S i)).setv (R 38) (a' - i)) Dg (R 34)
    (Ls off d bm p S ws l i)

theorem circD_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (rest : ℕ → List Bool) (G p bm d off U : ℕ)
    (l : List Bool) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hp : 2 ≤ p) (hbm : bm < p)
    (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm) (hdv : σ.val (R 36) = d) (hov : σ.val (R 4) = off)
    (hz : Zs R σ cL) (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hpU : p ≤ U) (hdU : d ≤ U) (hlU : (Ls off d bm p S ws l a').length + off + Os S a' + 2 ≤ U) (haU : a' ≤ U)
    (hU : 2 * U + 2 ≤ cap) :
    WExec cap (circW (R 38) (fun i => cBodyDW R (Pay i) Dg)) (circDSt R σ Dg a' G off d bm p S m ws l 0)
      (circDSt R σ Dg a' G off d bm p S m ws l a') (4 * (cDB U + 3) + 3) := by
  refine circ_spec cap (R 38) (fun i => cBodyDW R (Pay i) Dg) a' (cDB U) ha (by omega)
    (circDSt R σ Dg a' G off d bm p S m ws l) (fun k _ => by simp [circDSt, outAt]) ?_
  intro i hi
  have hci := hc i.val hi
  have hlen : (cD i.val).length = (natWord (S i.val)).length + (natWord (m i.val)).length +
      ((zs i.val).flatMap intWord).length + ((ws i.val).flatMap intWord).length + (rest i.val).length := by
    rw [hci]; simp only [List.length_append]; ring
  have hwl := fm_len_ge (ws i.val)
  have hzl := fm_len_ge (zs i.val)
  have hwsi := hws i.val hi
  have hLm := Ls_mono off d bm p S ws l (i.val + 1) a' hi
  have hOm := Os_mono S (i.val + 1) a' hi
  have hGi := Gs_le G m i.val
  have hBi := Bs_lt bm p hp i.val
  have hLs1 : Ls off d bm p S ws l (i.val + 1) = Ls off d bm p S ws l i.val ++
      emitList off d (Bs bm p i.val) p (Os S i.val) (ws i.val) := rfl
  have hOs1 : Os S (i.val + 1) = Os S i.val + S i.val := rfl
  have dx := cBodyD_spec cap R (Pay i) Dg (hPD i) (S i.val) (m i.val) (Gs G m i.val) (zs i.val) (ws i.val) (cD i.val)
    (rest i.val) p (Bs bm p i.val) bm d off (Os S i.val) U (Ls off d bm p S ws l i.val)
    ((circDSt R σ Dg a' G off d bm p S m ws l i.val).setv (R 38) (a' - i.val - 1))
    (by simp [circDSt, outAt, Function.update_apply, hPD i, hst i hi])
    (by simp [circDSt, outAt, Function.update_apply, hPD i, hs i hi]) hci (hzs i.val hi) hwsi (hm i.val hi)
    (by omega) hBi hbm (by simp [circDSt, outAt]) (by simp [circDSt, outAt]) (by simp [circDSt, outAt])
    (by simp [circDSt, outAt]) (by simp [circDSt, outAt]) (by simp [circDSt, outAt, h23])
    (by simp [circDSt, outAt, hP]) (by simp [circDSt, outAt, hdv]) (by simp [circDSt, outAt, hov])
    (by simp [circDSt, outAt])
    (fun r hr => by
      have r17 : r ≠ 17 := by rintro rfl; revert hr; decide
      have r25 : r ≠ 25 := by rintro rfl; revert hr; decide
      have r37 : r ≠ 37 := by rintro rfl; revert hr; decide
      have r38 : r ≠ 38 := by rintro rfl; revert hr; decide
      have r34 : r ≠ 34 := by rintro rfl; revert hr; decide
      have := hz r hr
      simp [circDSt, outAt, Function.update_apply, R.injective.ne r17, R.injective.ne r25, R.injective.ne r37,
        R.injective.ne r38, R.injective.ne r34, this])
    (hcU i.val hi) (hmU i.val hi) (le_trans hGi hGU) hpU hdU (by rw [← hLs1]; omega) hU
  refine WExec.cast cap dx ?_ (cDCost_le _ _ _ _ _ _ _ _ _ _ U (by have := hcU i.val hi; omega) (hmU i.val hi)
    (le_trans hGi hGU) (by have := hcU i.val hi; omega) (hcU i.val hi) hpU hdU (by omega) (by omega)
    (by have := hcU i.val hi; omega))
  show _ = outAt ((((σ.setv (R 17) (Gs G m i.val / m i.val)).setv (R 25) (Bs bm p i.val * bm % p)).setv (R 37)
    (Os S i.val + S i.val)).setv (R 38) (a' - (i.val + 1))) Dg (R 34) (Ls off d bm p S ws l i.val ++
      emitList off d (Bs bm p i.val) p (Os S i.val) (ws i.val))
  rw [show a' - (i.val + 1) = a' - i.val - 1 by omega]
  unfold circDSt
  clear dx hz
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

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
