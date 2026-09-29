import Proof.Wire_3_5.UnionMachine.CWParYb

/-! # C6 front, U5, the code writers: the parity writer's stages in powers of `Y`

Uniform bounds, in powers of `Y ≥ 9`, for the parity writer's (P3:3092-3094) docked machines: base's serializer
(`ser_y`, `serBits_y`), base's tagged cons (`consB_y`, `consBits_y`), base's pair node (`pairB_y`, `pairBits_y`), and
the copies (`cp_y`); then the prefix (**`pre_y`**, `Y^39`) and the bottoms' loop (**`loop_y`**, `Y^64`), at `Y = 9n + 9`.

Paper quantity: none (the writer's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParTime
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (cons)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serCost)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSize
open NearCubicWires.WireExponent3_5.UnionMachine.CWParYb
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (preCost WLv SBv P3v wlGs sbGs)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParLoop (loopCost)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParFit (CP cwP)

variable {Y : ℕ}

theorem ser_y (hY : 9 ≤ Y) (gs : List (List Bool)) (e : ℕ) (hm : PCPSerializerMass.mass gs ≤ Y ^ e) :
    serCost gs ≤ Y ^ (12 * e + 25) := by
  have h1 := serCost_le gs
  have h2 : PCPSerializerMass.mass gs + 1 ≤ Y ^ (e + 1) := by
    have := ylin hY hm 1 1 1 (by norm_num); simpa using this
  have h3 := ypw 12 h2
  have h4 := ylin hY h3 2000000000000 6 13 (by norm_num)
  have e1 : (e + 1) * 12 + 13 = 12 * e + 25 := by ring
  rw [e1] at h4
  omega

theorem serBits_y (hY : 9 ≤ Y) (gs : List (List Bool)) (e : ℕ) (hm : PCPSerializerMass.mass gs ≤ Y ^ e) :
    (PCPTraversal.code gs).bits.length ≤ Y ^ (5 * e + 6) := by
  have h1 := ser_bits gs
  have h2 : PCPSerializerMass.mass gs + 1 ≤ Y ^ (e + 1) := by
    have := ylin hY hm 1 1 1 (by norm_num); simpa using this
  have h3 := ypw 5 h2
  have h4 := ylin hY h3 3 0 1 (by norm_num)
  have e1 : (e + 1) * 5 + 1 = 5 * e + 6 := by ring
  rw [e1] at h4
  omega

theorem consBits_y (hY : 9 ≤ Y) (a b e : ℕ) (ha : a.bits.length ≤ Y ^ e) (hb : b.bits.length ≤ Y ^ e) :
    (cons a b).bits.length ≤ Y ^ (e + 3) := by
  have h1 := cons_bits a b
  have h2 := yadd hY ha hb
  have h3 := ylin hY h2 4 8 2 (by norm_num)
  have e1 : e + 1 + 2 = e + 3 := by omega
  rw [e1] at h3
  omega

theorem consB_y (hY : 9 ≤ Y) (a b e : ℕ) (ha : a.bits.length ≤ Y ^ e) (hb : b.bits.length ≤ Y ^ e) :
    PCPPRequestTaggedCons.budget a b ≤ Y ^ (2 * e + 8) := by
  have h1 := consB_le a b
  have h2 := yadd hY ha hb
  have h3 : a.bits.length + b.bits.length + 2 ≤ Y ^ (e + 2) := by
    have := ylin hY h2 1 2 1 (by norm_num); simp at this; omega
  have h4 := ypw 2 h3
  have h5 := ylin hY h4 6000 0 4 (by norm_num)
  have e1 : (e + 2) * 2 + 4 = 2 * e + 8 := by ring
  rw [e1] at h5
  have h6 : 6000 * (a.bits.length + b.bits.length + 2) ^ 2 ≤ 6000 * Y ^ ((e + 2) * 2) := Nat.mul_le_mul_left _ h4
  omega

theorem cp_y (hY : 9 ≤ Y) (x e : ℕ) (hx : x ≤ Y ^ e) : 2 * (14 * x + 5) + 2 ≤ Y ^ (e + 2) := by
  have := ylin hY hx 28 12 2 (by norm_num)
  omega

/-- A constant multiple. -/
theorem ybig (hY : 9 ≤ Y) {x : ℕ} (e c k : ℕ) (hc : c ≤ 9 ^ k) (hx : x ≤ c * Y ^ e) : x ≤ Y ^ (e + k) := by
  have h := ylin hY (le_refl (Y ^ e)) c 0 k (by simpa using hc)
  simp only [add_zero] at h
  exact hx.trans h

theorem zero_bits_y (e : ℕ) : (0 : ℕ).bits.length ≤ Y ^ e := by
  have : (0 : ℕ).bits.length = 0 := by decide
  omega

/-! ## The prefix -/

theorem wl_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) : (WLv l).bits.length ≤ Y ^ 6 := by
  have w := (widths l).wl
  rw [← hYn] at w
  exact ybig (by omega) 5 3 1 (by norm_num) w

theorem sb_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) : (SBv l).bits.length ≤ Y ^ 6 := by
  have w := (widths l).sb
  rw [← hYn] at w
  exact ybig (by omega) 5 3 1 (by norm_num) w

theorem p3_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) : (P3v l).bits.length ≤ Y ^ 7 := by
  have w := (widths l).p3
  rw [← hYn] at w
  have h : 12 * Y ^ 5 + 8 ≤ Y ^ 7 := ylin (by omega : 9 ≤ Y) (le_refl (Y ^ 5)) 12 8 2 (by norm_num)
  omega

/-- **The prefix within `Y^39`.** -/
theorem pre_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) : preCost l ≤ Y ^ 39 := by
  have hY : 9 ≤ Y := by omega
  have n1 : l.length ≤ Y ^ 1 := by rw [pow_one]; omega
  have wl6 := wl_y l Y hYn
  have sb6 := sb_y l Y hYn
  have p37 := p3_y l Y hYn
  have a1 := yle hY (show _ ≤ 37 by norm_num) (ylin hY n1 144 20 3 (by norm_num))
  have a2 := yle hY (show _ ≤ 37 by norm_num) (ser_y hY (wlGs l) 1 (by have := mass_wl l; rw [pow_one]; omega))
  have a3 := yle hY (show _ ≤ 37 by norm_num) (cp_y hY _ 6 wl6)
  have a4 := yle hY (show _ ≤ 37 by norm_num) (ser_y hY (sbGs l) 1 (by rw [mass_sb, pow_one]; omega))
  have a5 := yle hY (show _ ≤ 37 by norm_num) (cp_y hY _ 6 sb6)
  have a6 := yle hY (show _ ≤ 37 by norm_num) (consB_y hY (SBv l) 0 6 sb6 (zero_bits_y 6))
  have a7 := yle hY (show _ ≤ 37 by norm_num) (cp_y hY _ 7 p37)
  have a8 := yle hY (show _ ≤ 37 by norm_num) (ylin hY n1 18 4 2 (by norm_num))
  have hb : 81 * Y ^ 37 ≤ Y ^ (37 + 2) := ybig hY 37 81 2 (by norm_num) le_rfl
  have hp := ypos hY 37
  unfold preCost
  show _ ≤ Y ^ (37 + 2)
  omega

/-! ## The bottoms' loop -/

theorem cp_le : CP ≤ 9 ^ 27 := by unfold CP; norm_num

theorem value_y (n Y : ℕ) (hYn : Y = 9 * n + 9) : BlockPlatform.UnaryCalc.value 24 CP n ≤ Y ^ 51 := by
  have hY : 9 ≤ Y := by omega
  have p24 : (n + 1) ^ 24 ≤ Y ^ 24 := Nat.pow_le_pow_left (by omega) 24
  exact ym (yc hY _ 27 cp_le) p24

theorem cwP_y (n Y : ℕ) (hYn : Y = 9 * n + 9) : cwP n ≤ Y ^ 26 := by
  have hY : 9 ≤ Y := by omega
  have h : cwP n ≤ 3000000000000 * Y ^ 12 := by unfold cwP; rw [hYn]
  exact ybig hY 12 3000000000000 14 (by norm_num) h

theorem power_y (n Y : ℕ) (hYn : Y = 9 * n + 9) : PCPSerializerCapacity.Power.budget 24 CP n ≤ Y ^ 62 := by
  have hY : 9 ≤ Y := by omega
  have hpoly : PCPSerializerCapacity.Power.budget 24 CP n ≤
      BlockPlatform.UnaryCalc.polyCoefficient 24 CP * (n + 1) ^ (24 + 1) :=
    BlockPlatform.UnaryCalc.poly_cost_polyBounded 24 CP n
  have hpc : BlockPlatform.UnaryCalc.polyCoefficient 24 CP ≤ 9 ^ 37 := by
    unfold BlockPlatform.UnaryCalc.polyCoefficient CP; norm_num
  have p25 : (n + 1) ^ (24 + 1) ≤ Y ^ 25 := Nat.pow_le_pow_left (by omega) 25
  exact hpoly.trans (ym (yc hY _ 37 hpc) p25)

/-- **The bottoms' loop within `Y^64`.** -/
theorem loop_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) :
    loopCost (l.count true) l.length CP (cwP l.length) ≤ Y ^ 64 := by
  have hY : 9 ≤ Y := by omega
  have hk : l.count true ≤ l.length := List.count_le_length
  have k1 : l.count true ≤ Y ^ 1 := by rw [pow_one]; omega
  have hV := value_y l.length Y hYn
  have hc := yle hY (show 26 ≤ 51 by norm_num) (cwP_y l.length Y hYn)
  have hP := power_y l.length Y hYn
  have hp := ypos hY 51
  have hb1 : 81 * Y ^ 51 ≤ Y ^ (51 + 2) := ybig hY 51 81 2 (by norm_num) le_rfl
  have hin : cwP l.length + 1 + (2 * BlockPlatform.UnaryCalc.value 24 CP l.length + 4 + 1 + 0) + 2 ≤ Y ^ (51 + 2) := by
    omega
  have hm := ym k1 hin
  have hm' := yle hY (show 1 + (51 + 2) ≤ 62 by norm_num) hm
  have hV' := yle hY (show 51 ≤ 62 by norm_num) hV
  have k62 := yle hY (show 1 ≤ 62 by norm_num) k1
  have hb : 81 * Y ^ 62 ≤ Y ^ (62 + 2) := ybig hY 62 81 2 (by norm_num) le_rfl
  have hp2 := ypos hY 62
  unfold loopCost
  show _ ≤ Y ^ (62 + 2)
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.CWParTime
