import Proof.Wire_3_5.UnionMachine.NumsC5Base
import Proof.Wire_3_5.FinalPass.FpInLenBase

/-! # NW phase (c), part 6: **`phC x l : NumsPh2.PhC x l`** (the deliverable)

`cProg` per gate (`c_r`, `KT`, `ZT` of `F`), compiled; capacity need `(KT + 2c_r + 60)·2^{ZT+2}·(|fpIn|+1)^{ZT+2}`
(the width `T_f`, the star numbers' and the reader's needs, `n ≤ |fpIn|`); steps
`2000·(KT + c_r + ZT + 10)²·2^{ZT+2}·(|fpIn|+1)^{ZT+2}`; the exponent `ZT = ZTe l fe` reads `(l, fe)` only.

* `rsC_length`, **`cCost_le`**, `KnC`, `DnC`, `CsC`, `DsC`, **`phC`**.

Paper quantities of the main type: `n`, the mode, `e = n − k`, `T_f` (P3:3044-3048, P3:1188-1189). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

theorem rsC_length : rsC.length = 30 := by simp [rsC]

/-- **(c)'s steps below `2000·K²·(n+2)^{ZT+2}`**, `K = KT + c_r + ZT + 10`. -/
theorem cCost_le (n cr k KT ZT : ℕ) (hk : k ≤ n) (hZT : 1 ≤ ZT) (hKT : 1 ≤ KT) :
    frontCost n + 1 + restCost n cr k KT ZT (KT * (n + 2) ^ ZT) ≤
      2000 * (KT + cr + ZT + 10) ^ 2 * (n + 2) ^ (ZT + 2) := by
  obtain ⟨K, hK⟩ : ∃ v, v = KT + cr + ZT + 10 := ⟨_, rfl⟩
  rw [← hK]
  have hW1 : n + 2 ≤ (n + 2) ^ ZT := by
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hZT
  have eV : (n + 2) ^ (ZT + 2) = (n + 2) ^ ZT * ((n + 2) * (n + 2)) := by ring
  have hpow := CopyNat.two_pow_natBitLength_le n
  have hnb : natBitLength n ≤ n + 1 := by
    show Nat.log 2 n + 1 ≤ n + 1
    have := Nat.log_le_self 2 n; omega
  have f1 : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 200 * ((n + 2) * (n + 2)) := by
    calc (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ (n + 3) * (80 * n + 120) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 200 * ((n + 2) * (n + 2)) := by nlinarith
  unfold frontCost restCost StarNums.starCost
  rw [rsC_length, eV]
  obtain ⟨W, hWd⟩ : ∃ v, v = (n + 2) ^ ZT := ⟨_, rfl⟩
  rw [← hWd] at hW1 ⊢
  obtain ⟨N2, hN2⟩ : ∃ v, v = (n + 2) * (n + 2) := ⟨_, rfl⟩
  have e400 : 400 * (n + 2) * (n + 2) = 400 * N2 := by rw [hN2]; ring
  have e25 : 25 * 0 * (n + 2) = 0 := by ring
  rw [e400, e25]
  rw [← hN2] at f1 ⊢
  have hN2n : n + 2 ≤ N2 := by rw [hN2]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hWN : W * (n + 2) ≤ W * N2 := Nat.mul_le_mul_left _ hN2n
  have hW2 : 2 ≤ W := by omega
  have hN1 : N2 ≤ W * N2 := Nat.le_mul_of_pos_left _ (by omega)
  have hK1 : 1 ≤ K := by omega
  have hKK : K ≤ K * K := Nat.le_mul_of_pos_left _ hK1
  obtain ⟨V, hVd⟩ : ∃ v, v = W * N2 := ⟨_, rfl⟩
  rw [← hVd] at hWN hN1 ⊢
  have hV1 : 1 ≤ V := by omega
  have hWV : W ≤ V := by rw [hVd]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hKTK : KT ≤ K := by omega
  have g1 : KT * W ≤ K * V := Nat.mul_le_mul hKTK hWV
  have g2 : ZT * (60 * (KT * W + 1) * (n + 2 + 1) + 1) ≤ 241 * (K * K * V) := by
    have a1 : KT * W + 1 ≤ 2 * (K * W) := by
      have := Nat.mul_le_mul_right W (show KT ≤ K by omega); nlinarith
    have a2 : (KT * W + 1) * (n + 2 + 1) ≤ 2 * (K * W) * (2 * (n + 2)) := Nat.mul_le_mul a1 (by omega)
    have a3 : 2 * (K * W) * (2 * (n + 2)) = 4 * (K * (W * (n + 2))) := by ring
    have a4 : K * (W * (n + 2)) ≤ K * V := Nat.mul_le_mul_left _ hWN
    have a5 : 60 * (KT * W + 1) * (n + 2 + 1) + 1 ≤ 241 * (K * V) := by
      have : 60 * (KT * W + 1) * (n + 2 + 1) = 60 * ((KT * W + 1) * (n + 2 + 1)) := by ring
      have hKV : 1 ≤ K * V := Nat.mul_pos hK1 hV1
      omega
    calc ZT * (60 * (KT * W + 1) * (n + 2 + 1) + 1) ≤ K * (241 * (K * V)) :=
          Nat.mul_le_mul (by omega) a5
      _ = 241 * (K * K * V) := by ring
  have g3 : K * V ≤ K * K * V := Nat.mul_le_mul_right _ hKK
  have g4 : V ≤ K * V := Nat.le_mul_of_pos_left _ hK1
  have g5 : K ≤ K * V := Nat.le_mul_of_pos_right _ hV1
  have e : 2000 * K ^ 2 * V = 2000 * (K * K * V) := by ring
  rw [e]
  have hk' : k ≤ n := hk
  omega

section Gate
variable (x : ℕ) (l : Literals)

theorem npow_le (n X Z : ℕ) (h : n + 1 ≤ X) : (n + 2) ^ Z ≤ 2 ^ Z * X ^ Z := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
