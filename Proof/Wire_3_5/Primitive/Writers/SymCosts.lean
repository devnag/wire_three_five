import Proof.Wire_3_5.Primitive.Writers.SymCost
import Proof.Wire_3_5.Primitive.Writers.HashCosts
import Proof.Wire_3_5.Primitive.Writers.PopBankDock

/-! # SYM leaf, part 4: the SYM unit decode's costs, polynomially

The SYM unit decode's cost `Dc` (`SymDec.symNU`'s second argument: the request parse, the counts, the star numbers
and the cap, the numbers stage, the banks' bound `Bb`) is a small polynomial in the register capacity `cap` once
`cap` exceeds the call's small values:

* `reqParseCost_le` (`≤ 1000(cap+2)²`), `countsCost_le` (`≤ 100(cap+2)`), **`starCapCost_le`**
  (`≤ 2·10⁶(cap+2)³`), `fbCost_le` (`≤ 7000(cap+2)²`), `pbCost_le` (`= 52000(cap+2)²`), **`decCost_le`** (the whole
  `Dc ≤ 3·10⁶(cap+2)³ + Bb`).

Paper quantity of the main type: the SYM writer's per-unit cost (the SYM tape's units, P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
open NearCubicWires NearCubicWires.WireExponent3_5

theorem nbl_small4 (x : ℕ) (hx : x ≤ 4) : (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ 2000 := by
  have h1 : natBitLength x ≤ 3 := by
    unfold natBitLength
    have := Nat.log_mono_right (b := 2) hx
    have e : Nat.log 2 4 = 2 := by decide
    omega
  have h2 : 2 ^ natBitLength x ≤ 8 := by
    calc 2 ^ natBitLength x ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h1
      _ = 8 := by norm_num
  have := Nat.mul_le_mul (show natBitLength x + 2 ≤ 5 by omega) (show 40 * 2 ^ natBitLength x + 40 ≤ 360 by omega)
  omega

theorem reqParseCost_le (n a nc Kb cap : ℕ) (hn : n ≤ cap) (ha : a ≤ 4) (hnc : nc ≤ 4) (hK : Kb ≤ cap) :
    SymDec.reqParseCost n a nc Kb ≤ 2000 * ((cap + 2) * (cap + 2)) := by
  have hbn := PrimAsm.CopyNat.natBitLength_le_self_succ n
  have hpw := PrimAsm.CopyNat.two_pow_natBitLength_le n
  have fB : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 360 * ((n + 1) * (n + 1)) := by
    have := Nat.mul_le_mul (show natBitLength n + 2 ≤ 3 * (n + 1) by omega)
      (show 40 * 2 ^ natBitLength n + 40 ≤ 120 * (n + 1) by omega)
    have e : 3 * (n + 1) * (120 * (n + 1)) = 360 * ((n + 1) * (n + 1)) := by ring
    omega
  have fa := nbl_small4 a ha
  have fc := nbl_small4 nc hnc
  have g1 : (n + 1) * (n + 1) ≤ (cap + 2) * (cap + 2) := Nat.mul_le_mul (by omega) (by omega)
  have g2 : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_of_pos_left _ (by omega)
  have g3 : a * (20 * Kb + 20 + 4) ≤ 4 * (20 * cap + 24) := Nat.mul_le_mul ha (by omega)
  have g4 : 2 * (cap + 2) ≤ (cap + 2) * (cap + 2) := Nat.mul_le_mul_right _ (by omega)
  unfold SymDec.reqParseCost
  omega

theorem countsCost_le (nc Cmax Sm cap : ℕ) (hnc : nc ≤ 4) (hC : Cmax ≤ cap) (hS : Sm ≤ cap) :
    SymDec.countsCost nc Cmax Sm ≤ 200 * (cap + 2) := by
  unfold SymDec.countsCost
  have : nc * (3 * Cmax + 3 + 4) ≤ 4 * (3 * cap + 7) := Nat.mul_le_mul hnc (by omega)
  omega

theorem starCapCost_le (n cr fe t sp L cap : ℕ) (hn : n + 2 ≤ cap) (hcr : cr ≤ cap) (hfe : fe ≤ cap) (ht : t ≤ cap)
    (hsp : sp ≤ cap) (hL : L ≤ cap) :
    SymDec.starCapCost n cr fe t sp L cap ≤ 2000000 * ((cap + 2) * (cap + 2) * (cap + 2)) := by
  obtain ⟨c, hc⟩ : ∃ x, x = cap + 2 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x, x = c * c := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x, x = c * c * c := ⟨_, rfl⟩
  have hsq : UnaryPow.sq cap = 200 * c2 := by unfold UnaryPow.sq; rw [hc2, hc]; ring
  have hst : StarNums.starCost n cr fe ≤ 400 * c2 + 30 * c + 25 * c2 := by
    unfold StarNums.starCost
    have g1 : (n + 2) * (n + 2) ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
    have g4 : fe * (n + 2) ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
    have e1 : 400 * (n + 2) * (n + 2) = 400 * ((n + 2) * (n + 2)) := by ring
    have e2 : 25 * fe * (n + 2) = 25 * (fe * (n + 2)) := by ring
    rw [e1, e2]; rw [← hc2] at g1 g4; omega
  have hc1 : 1 ≤ c := by omega
  have gcc : c ≤ c2 := by rw [hc2]; exact Nat.le_mul_of_pos_left _ hc1
  have gc23 : c2 ≤ c3 := by rw [hc3, hc2]; exact Nat.le_mul_of_pos_right _ hc1
  have g5 : (t + 5) * (40 * (200 * c2)) ≤ 8000 * c3 + 40000 * c2 := by
    have e : (t + 5) * (40 * (200 * c2)) = 8000 * (t * c2) + 40000 * c2 := by ring
    have h : t * c2 ≤ c * c2 := Nat.mul_le_mul_right _ (by omega)
    have e3 : c * c2 = c3 := by rw [hc3, hc2]; ring
    omega
  have g6 : (cap * 1 + 2 * 1) * 0 = 0 := by ring
  have g7 : ((cap + 2) * 200 + 1500) * (200 * c2) ≤ 340000 * c3 := by
    have e : ((cap + 2) * 200 + 1500) * (200 * c2) = 40000 * (c * c2) + 300000 * c2 := by rw [← hc]; ring
    have e3 : c * c2 = c3 := by rw [hc3, hc2]; ring
    omega
  have eR : 2000000 * ((cap + 2) * (cap + 2) * (cap + 2)) = 2000000 * c3 := by rw [hc3, hc]
  rw [eR]
  unfold SymDec.starCapCost
  rw [hsq]
  omega

theorem fbCost_le (c : ℕ) : SymDec.fbCost c ≤ 7000 * ((c + 2) * (c + 2)) := by
  unfold SymDec.fbCost UnaryPow.sq
  have g : 2 * (c + 2) ≤ (c + 2) * (c + 2) := Nat.mul_le_mul_right _ (by omega)
  have e : 200 * (c + 2) * (c + 2) = 200 * ((c + 2) * (c + 2)) := by ring
  rw [e]
  omega

theorem pbCost_eq (c : ℕ) : SymDec.pbCost c = 52000 * ((c + 2) * (c + 2)) := by
  unfold SymDec.pbCost UnaryPow.sq; ring

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
