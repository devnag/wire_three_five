import Proof.Wire_3_5.Primitive.SeedFix.TS4O

/-! # thrStage4U, part 14: the prep's time is polynomial

P3:3071-3091 ("the preprocessing … runs in time polynomial in `n`") and P3:3114-3115: at the gate, the prep's stage cost
`p0StageCost` (the request parse, the THR cap `B_T(n)`: PA's schedule `t = O(L)`, the sparse count, `capM`'s squares;
the count `V = W + (n+1)^{26}`) is at most `Kp·(n + W + 3)^{Dp}`, the degree fixed by the literals, the coefficient by
`c_r`:

* `Dp`, `Kp`, **`p0Stage_le`**.

Paper quantities of the main type: the prep's step count, polynomial in `n + W`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.SymDec

variable (l : Literals)

/-- The prep's degree. -/
noncomputable def Dp : ℕ := PrimAsm.CallIndexR.capZR l + gateCsp l + 30

/-- The prep's coefficient. -/
noncomputable def Kp (cr : ℕ) : ℕ := 100000000 * (SymSizes.schedJ l + cr + PrimAsm.CallIndexR.capK cr + 1)

theorem nbl_small (v : ℕ) : natBitLength v + 2 ≤ 2 ^ (natBitLength v) + 2 := by
  have := Nat.lt_two_pow_self (n := natBitLength v); omega

theorem a1_le (n B : ℕ) (h : n + 3 ≤ B) : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 120 * B ^ 2 := by
  have pn := W6.pow_nbl n
  have e2n : 2 ^ (natBitLength n + 1) = 2 * 2 ^ natBitLength n := by rw [pow_succ]; ring
  have nbln : natBitLength n ≤ n + 1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
  have hm := Nat.mul_le_mul (show natBitLength n + 2 ≤ B by omega) (show 40 * 2 ^ natBitLength n + 40 ≤ 120 * B by omega)
  calc _ ≤ B * (120 * B) := hm
    _ = 120 * B ^ 2 := by ring

theorem a2_le (a : ℕ) (ha : a ≤ 4) : (natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) ≤ 12 * 440 := by
  have pa := W6.pow_nbl a
  have e2a : 2 ^ (natBitLength a + 1) = 2 * 2 ^ natBitLength a := by rw [pow_succ]; ring
  have ba := nbl_small a
  exact Nat.mul_le_mul (by omega) (by omega)

theorem sq_le (W B : ℕ) (h : W + 3 ≤ B) : UnaryPow.sq (2 * W + 2) ≤ 800 * B ^ 2 := by
  unfold UnaryPow.sq
  have hm := Nat.mul_le_mul (show 2 * W + 2 + 2 ≤ 2 * B by omega) (show 2 * W + 2 + 2 ≤ 2 * B by omega)
  calc 200 * (2 * W + 2 + 2) * (2 * W + 2 + 2) = 200 * ((2 * W + 2 + 2) * (2 * W + 2 + 2)) := by ring
    _ ≤ 200 * (2 * B * (2 * B)) := Nat.mul_le_mul_left _ hm
    _ = 800 * B ^ 2 := by ring

theorem a5_le (t J W B : ℕ) (ht : t ≤ J * B + 1) (h : W + 3 ≤ B) :
    (t + 5) * (40 * UnaryPow.sq (2 * W + 2)) ≤ 32000 * (J * B ^ 3) + 192000 * B ^ 2 := by
  have hs := sq_le W B h
  have hm := Nat.mul_le_mul (show t + 5 ≤ J * B + 6 by omega) (show 40 * UnaryPow.sq (2 * W + 2) ≤ 32000 * B ^ 2 by omega)
  calc _ ≤ (J * B + 6) * (32000 * B ^ 2) := hm
    _ = 32000 * (J * B ^ 3) + 192000 * B ^ 2 := by ring

theorem a6_le (W B : ℕ) (h : W + 3 ≤ B) :
    ((2 * W + 2 + 2) * 200 + 1500) * UnaryPow.sq (2 * W + 2) ≤ 1520000 * B ^ 3 := by
  have hs := sq_le W B h
  have hm := Nat.mul_le_mul (show (2 * W + 2 + 2) * 200 + 1500 ≤ 1900 * B by omega) hs
  calc _ ≤ 1900 * B * (800 * B ^ 2) := hm
    _ = 1520000 * B ^ 3 := by ring

theorem rowBt_B (n B : ℕ) (h : n + 3 ≤ B) :
    Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n ≤ SymSizes.schedJ l * B + 1 := by
  have ht := SymSizes.rowBt_le l n
  have hcl : Nat.clog 2 (n + 2) ≤ n + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hJ : SymSizes.schedJ l * (Nat.clog 2 (n + 2) + 1) ≤ SymSizes.schedJ l * B := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The prep's time at the gate.** -/
theorem p0Stage_le (cr n W a nc : ℕ) (ha : a ≤ 4) (hnc : nc ≤ 2) :
    p0StageCost n cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) a nc W W ≤
      Kp l cr * (n + W + 3) ^ Dp l := by
  obtain ⟨B, hB⟩ : ∃ B, B = n + W + 3 := ⟨_, rfl⟩
  have hB3 : 3 ≤ B := by omega
  have A1 := a1_le n B (by omega)
  have A2 := a2_le a ha
  have A4 := a2_le nc (by omega)
  have A3 : a * (20 * W + 20 + 4) ≤ 4 * (20 * W + 20 + 4) := Nat.mul_le_mul_right _ ha
  have hsq := sq_le W B (by omega)
  have A5 := a5_le _ _ W B (rowBt_B l n B (by omega)) (by omega)
  have A6 := a6_le W B (by omega)
  have hL : Ledger.Lq n ≤ n + 2 := PrimAsm.CallIndex.Lq_le_N n
  have h26 : (n + 1) ^ 26 ≤ B ^ 26 := Nat.pow_le_pow_left (by omega) _
  obtain ⟨J, hJd⟩ : ∃ J, J = SymSizes.schedJ l := ⟨_, rfl⟩
  rw [← hJd] at A5
  -- the powers with symbolic exponents, as atoms
  obtain ⟨X, hXd⟩ : ∃ X, X = B ^ Dp l := ⟨_, rfl⟩
  have up : ∀ d, d ≤ Dp l → B ^ d ≤ X := fun d hd => hXd ▸ Nat.pow_le_pow_right (by omega) hd
  have X1 : 1 ≤ X := hXd ▸ Nat.one_le_pow _ _ (by omega)
  have XB : B ≤ X := by have := up 1 (by unfold Dp; omega); rwa [pow_one] at this
  have X2 := up 2 (by unfold Dp; omega)
  have X3 := up 3 (by unfold Dp; omega)
  have X26 := up 26 (by unfold Dp; omega)
  have hsp : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ X := by
    have h0 : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ (n + 2) ^ (gateCsp l + 3) :=
      PrimAsm.CallIndex.sp_le l n
    have h1 : (n + 2) ^ (gateCsp l + 3) ≤ B ^ (gateCsp l + 3) := Nat.pow_le_pow_left (by omega) _
    exact h0.trans (h1.trans (up _ (by unfold Dp; omega)))
  have hcap : capTL l cr n ≤ PrimAsm.CallIndexR.capK cr * X := by
    have h0 : capTL l cr n ≤ PrimAsm.CallIndexR.capK cr * (n + 2) ^ PrimAsm.CallIndexR.capZR l := capTL_le l cr n
    have h1 : (n + 2) ^ PrimAsm.CallIndexR.capZR l ≤ B ^ PrimAsm.CallIndexR.capZR l := Nat.pow_le_pow_left (by omega) _
    exact h0.trans (Nat.mul_le_mul_left _ (h1.trans (up _ (by unfold Dp; omega))))
  have ecap : capTOf cr n (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) = capTL l cr n := rfl
  have JX : J * B ^ 3 ≤ J * X := Nat.mul_le_mul_left _ X3
  have cX : cr ≤ cr * X := Nat.le_mul_of_pos_right _ X1
  have eK : Kp l cr * (n + W + 3) ^ Dp l = 100000000 * (J * X) + 100000000 * (cr * X) +
      100000000 * (PrimAsm.CallIndexR.capK cr * X) + 100000000 * X := by
    rw [← hB, ← hXd, hJd]; unfold Kp; ring
  clear up hXd hJd
  unfold p0StageCost p0Cost reqParseCost capTCost
  rw [ecap, eK]
  omega

end NearCubicWires.WireExponent3_5.PrimT.TS4
