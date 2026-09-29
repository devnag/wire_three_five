import Proof.Wire_3_5.Primitive.Writers.HashKH
import Proof.Wire_3_5.Primitive.Writers.HashReady

/-! # (HASH (d4)), part 4: the HASH unit's and boot's costs, polynomially

The per-unit budget of the HASH writer adds the unit decode's numbers stage (`SymDec.hNCost`), the aux FILTER bank's
set-up (`SymDec.hbCost`), the loop's copy (`CellLoopD.cpCost`); the scrub bounds the boot (`ShellD.bootCost`). Each is
a small polynomial in the register capacity `cap` (with `n + 2 ≤ cap`, `c_r ≤ cap`) or in `|w|` and `n`:

* `cpCost_eq` (`17m + 9`), **`hNCost_le`** (`≤ 60000(cap+2)²`), **`hbCost_le`** (`≤ 5000(c+2)²`),
  **`bootCost_le`** (`≤ 4|w| + 100(n+2)`).

Paper quantity of the main type: the per-unit cost of the HASH writer's loop (the aux FILTER rows, P3:2220-2226). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

theorem cpCost_eq (m : ℕ) : PrimAsm.CellLoopD.cpCost m = 17 * m + 9 := by
  unfold PrimAsm.CellLoopD.cpCost; omega

theorem hNCost_le (n wl cr cap : ℕ) (hn : n + 2 ≤ cap) (hcr : cr ≤ cap) :
    SymDec.hNCost n wl cr cap ≤ 60000 * ((cap + 2) * (cap + 2)) := by
  have hbn := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have hpw := PrimAsm.CopyNat.two_pow_natBitLength_le n
  have fB : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 360 * ((n + 1) * (n + 1)) := by
    have := Nat.mul_le_mul (show natBitLength n + 2 ≤ 3 * (n + 1) by omega)
      (show 40 * 2 ^ natBitLength n + 40 ≤ 120 * (n + 1) by omega)
    have e : 3 * (n + 1) * (120 * (n + 1)) = 360 * ((n + 1) * (n + 1)) := by ring
    omega
  have g1 : (n + 1) * (n + 1) ≤ (cap + 2) * (cap + 2) := Nat.mul_le_mul (by omega) (by omega)
  have g2 : (n + 2) * (n + 2) ≤ (cap + 2) * (cap + 2) := Nat.mul_le_mul (by omega) (by omega)
  have g3 : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_of_pos_left _ (by omega)
  unfold SymDec.hNCost SymDec.hACost StarNums.starCost UnaryPow.sq
  have e1 : 400 * (n + 2) * (n + 2) = 400 * ((n + 2) * (n + 2)) := by ring
  have e2 : 200 * (cap + 2) * (cap + 2) = 200 * ((cap + 2) * (cap + 2)) := by ring
  have e3 : 25 * 0 * (n + 2) = 0 := by ring
  rw [e1, e2, e3]
  omega

theorem hbCost_le (c : ℕ) : SymDec.hbCost c ≤ 5000 * ((c + 2) * (c + 2)) := by
  unfold SymDec.hbCost UnaryPow.sq
  have g : c + 2 ≤ (c + 2) * (c + 2) := Nat.le_mul_of_pos_left _ (by omega)
  have e : 200 * (c + 2) * (c + 2) = 200 * ((c + 2) * (c + 2)) := by ring
  rw [e]
  omega

theorem bootCost_le (w : List Bool) (n : ℕ) : ShellD.bootCost w n 0 0 ≤ 4 * w.length + 100 * (n + 2) := by
  have b00 := UnaryCalc.poly_cost_polyBounded 0 0 n
  unfold ValidatorPolynomialDomination.PolyBounded at b00
  have e00 : UnaryCalc.polyCoefficient 0 0 * (n + 1) ^ (0 + 1) = 13 * (n + 1) := by
    simp [UnaryCalc.polyCoefficient]
  have v00 : UnaryCalc.value 0 0 n = 0 := by simp [UnaryCalc.value]
  have hbn := PrimAsm.CopyNat.natBitLength_le_self_succ n
  unfold ShellD.bootCost
  rw [v00]
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
