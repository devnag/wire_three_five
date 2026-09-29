import Proof.Wire_3_5.UnionMachine.CWParTime

/-! # C6 front, U5, the code writers: the parity writer's tops and suffix in powers of `Y`

The parity writer (P3:3092-3094) must run within a fixed polynomial of its input. With `Y ≥ 9 k + 9` (`k` the count):
* the tops' codes (`topSv_y`, `Y^11`; `topTv_y`, `Y^20`) and their machines' fuels (**`topSym_y`**, `Y^39`;
  **`topThr_y`**, `Y^44`);
* at `Y = 9 n + 9`, the suffix's fuel (**`suf_y`**, `Y^147`) for any top and tag codes within `Y^20`;
* **`core_y`**: the whole core's fuel within `Y^148`.

Paper quantity: none (the writer's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParTimeB
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (cons accOf gsOf code_gsOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serCost)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSize
open NearCubicWires.WireExponent3_5.UnionMachine.CWParYb
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTime
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (WLv P3v sbGs)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTop (oddL w10)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParGen (w9)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParTops (topSv topTv altV alltV altGs topSymCost topThrCost)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSuf (sufCost sufCode)
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (natCost)

variable {Y : ℕ}

/-! ## The tops' codes -/

theorem oddL_length (n : ℕ) : (oddL n).length = n := by unfold oddL; simp

theorem mass_odd (k : ℕ) : PCPSerializerMass.mass ((oddL (k + 1)).map fun b => [b]) = 3 * (k + 1) := by
  have h := mass_sb (oddL (k + 1))
  rw [oddL_length] at h
  exact h

theorem alt_len : ∀ k : ℕ, ((altGs k).flatMap frame).length = 9 * k
  | 0 => rfl
  | k + 1 => by
    have ih := alt_len k
    unfold altGs at ih ⊢
    rw [List.range_succ, List.map_append, List.flatMap_append, List.length_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_len]
    split_ifs <;> simp [w9, w10] <;> ring

theorem mass_alt (k : ℕ) : PCPSerializerMass.mass (altGs k) = 9 * k := by rw [mass_eq, alt_len]

theorem rep_eq (k : ℕ) : List.replicate k [true] = sbGs (List.replicate k true) := by
  unfold sbGs; rw [List.map_replicate]

theorem mass_rep (k : ℕ) : PCPSerializerMass.mass (List.replicate k [true]) = 3 * k := by
  rw [rep_eq, mass_sb, List.length_replicate]

theorem topSv_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : (topSv k).bits.length ≤ Y ^ 11 :=
  serBits_y hY _ 1 (by rw [mass_odd, pow_one]; omega)

theorem altV_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : (altV k).bits.length ≤ Y ^ 11 :=
  serBits_y hY _ 1 (by rw [mass_alt, pow_one]; omega)

theorem alltV_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : (alltV k).bits.length ≤ Y ^ 11 :=
  serBits_y hY _ 1 (by rw [mass_rep, pow_one]; omega)

theorem nine_bits_y (hY : 9 ≤ Y) (e : ℕ) (he : 1 ≤ e) : (9 : ℕ).bits.length ≤ Y ^ e := by
  have h : (9 : ℕ).bits.length = 4 := by decide
  have := yle hY he (yc hY 4 1 (by norm_num))
  omega

theorem c1_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : (cons (alltV k) 0).bits.length ≤ Y ^ 14 :=
  consBits_y hY _ _ 11 (alltV_y hY k hk) (zero_bits_y 11)

theorem c2_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : (cons 9 (cons (alltV k) 0)).bits.length ≤ Y ^ 17 :=
  consBits_y hY _ _ 14 (nine_bits_y hY 14 (by norm_num)) (c1_y hY k hk)

theorem topTv_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : (topTv k).bits.length ≤ Y ^ 20 :=
  consBits_y hY _ _ 17 (yle hY (by norm_num) (altV_y hY k hk)) (c2_y hY k hk)

/-! ## The tops' machines -/

/-- **The `SYM∘THR` top within `Y^39`.** -/
theorem topSym_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : topSymCost k ≤ Y ^ 39 := by
  have k1 : k ≤ Y ^ 1 := by rw [pow_one]; omega
  have a1 := yle hY (show _ ≤ 37 by norm_num) (ylin hY k1 48 62 3 (by norm_num))
  have a2 := yle hY (show _ ≤ 37 by norm_num) (ser_y hY ((oddL (k + 1)).map fun b => [b]) 1
    (by rw [mass_odd, pow_one]; omega))
  have a3 := yle hY (show _ ≤ 37 by norm_num) (cp_y hY _ 11 (topSv_y hY k hk))
  have hb : 81 * Y ^ 37 ≤ Y ^ (37 + 2) := ybig hY 37 81 2 (by norm_num) le_rfl
  have hp := ypos hY 37
  unfold topSymCost
  show _ ≤ Y ^ (37 + 2)
  omega

theorem frame9 : (frame w9).length = 9 := by rw [frame_len]; rfl
theorem frame3 : (frame [true, true]).length = 5 := by rw [frame_len]; rfl

/-- The `THR∘THR` top's fuel, summed over opaque operands. -/
theorem thrSum (hY : 9 ≤ Y) (k s1 s2 b1 b2 b3 b4 b5 c1 c2 c3 : ℕ) (a1 : 2 * (k * 60 + 10) + 2 ≤ Y ^ 42)
    (a2 : s1 ≤ Y ^ 42) (a3 : 2 * (14 * b1 + 5) + 2 ≤ Y ^ 42) (a4 : s2 ≤ Y ^ 42)
    (a5 : 2 * (14 * b2 + 5) + 2 ≤ Y ^ 42) (a6 : c1 ≤ Y ^ 42) (a7 : 2 * (14 * b3 + 5) + 2 ≤ Y ^ 42)
    (a8 : c2 ≤ Y ^ 42) (a9 : 2 * (14 * b4 + 5) + 2 ≤ Y ^ 42) (a10 : c3 ≤ Y ^ 42)
    (a11 : 2 * (14 * b5 + 5) + 2 ≤ Y ^ 42) :
    1 + 1 + ((2 * (k * 60 + 10) + 2) + 1 + (s1 + 1 + ((2 * (14 * b1 + 5) + 2) + 1 + (
      s2 + 1 + ((2 * (14 * b2 + 5) + 2) + 1 + (1 + 1 + (
      c1 + 1 + ((2 * (14 * b3 + 5) + 2) + 1 + (
      74 + 1 + (c2 + 1 + (
      (2 * (14 * b4 + 5) + 2) + 1 + (
      c3 + 1 + (
      (2 * (14 * b5 + 5) + 2) + 1 + 42))))))))))))) ≤ Y ^ 44 := by
  have hb : 81 * Y ^ 42 ≤ Y ^ (42 + 2) := ybig hY 42 81 2 (by norm_num) le_rfl
  have hp := ypos hY 42
  show _ ≤ Y ^ (42 + 2)
  linarith

/-- **The `THR∘THR` top within `Y^44`.** -/
theorem topThr_y (hY : 9 ≤ Y) (k : ℕ) (hk : 9 * k + 9 ≤ Y) : topThrCost k ≤ Y ^ 44 := by
  have k1 : k ≤ Y ^ 1 := by rw [pow_one]; omega
  have v1 := altV_y hY k hk
  have v2 := alltV_y hY k hk
  have v3 := c1_y hY k hk
  have v4 := c2_y hY k hk
  have v5 := topTv_y hY k hk
  have a1 := yle hY (show _ ≤ 42 by norm_num) (ylin hY k1 120 22 3 (by norm_num))
  have a1' : 2 * (k * 60 + 10) + 2 ≤ Y ^ 42 := by
    have e : 2 * (k * 60 + 10) + 2 = 120 * k + 22 := by ring
    rw [e]; exact a1
  unfold topThrCost
  rw [frame9, frame3]
  exact thrSum hY k (serCost (altGs k)) (serCost (List.replicate k [true])) (altV k).bits.length
    (alltV k).bits.length (cons (alltV k) 0).bits.length (cons 9 (cons (alltV k) 0)).bits.length (topTv k).bits.length
    (PCPPRequestTaggedCons.budget (alltV k) 0) (PCPPRequestTaggedCons.budget 9 (cons (alltV k) 0))
    (PCPPRequestTaggedCons.budget (altV k) (cons 9 (cons (alltV k) 0))) a1'
    (yle hY (show _ ≤ 42 by norm_num) (ser_y hY (altGs k) 1 (by rw [mass_alt, pow_one]; omega)))
    (yle hY (show _ ≤ 42 by norm_num) (cp_y hY _ 11 v1))
    (yle hY (show _ ≤ 42 by norm_num) (ser_y hY (List.replicate k [true]) 1 (by rw [mass_rep, pow_one]; omega)))
    (yle hY (show _ ≤ 42 by norm_num) (cp_y hY _ 11 v2))
    (yle hY (show _ ≤ 42 by norm_num) (consB_y hY (alltV k) 0 11 v2 (zero_bits_y 11)))
    (yle hY (show _ ≤ 42 by norm_num) (cp_y hY _ 14 v3))
    (yle hY (show _ ≤ 42 by norm_num) (consB_y hY 9 (cons (alltV k) 0) 14 (nine_bits_y hY 14 (by norm_num)) v3))
    (yle hY (show _ ≤ 42 by norm_num) (cp_y hY _ 17 v4))
    (yle hY (show _ ≤ 42 by norm_num) (consB_y hY (altV k) (cons 9 (cons (alltV k) 0)) 17
      (yle hY (by norm_num) v1) v4))
    (yle hY (show _ ≤ 42 by norm_num) (cp_y hY _ 20 v5))

/-! ## The suffix -/

/-- The suffix's fuel, summed over opaque operands. -/
theorem sufSum (hY : 9 ≤ Y) (s1 b1 s2 b2 c1 b3 c2 b4 c3 b5 c4 nc : ℕ) (a1 : s1 ≤ Y ^ 145)
    (a2 : 2 * (14 * b1 + 5) + 2 ≤ Y ^ 145) (a3 : s2 ≤ Y ^ 145) (a4 : 2 * (14 * b2 + 5) + 2 ≤ Y ^ 145)
    (a5 : c1 ≤ Y ^ 145) (a6 : 2 * (14 * b3 + 5) + 2 ≤ Y ^ 145) (a7 : c2 ≤ Y ^ 145)
    (a8 : 2 * (14 * b4 + 5) + 2 ≤ Y ^ 145) (a9 : c3 ≤ Y ^ 145) (a10 : 2 * (14 * b5 + 5) + 2 ≤ Y ^ 145)
    (a11 : c4 ≤ Y ^ 145) (a12 : 2 * nc + 2 ≤ Y ^ 145) :
    1 + 1 + (s1 + 1 + ((2 * (14 * b1 + 5) + 2) + 1 + (s2 + 1 + (
      (2 * (14 * b2 + 5) + 2) + 1 + (1 + 1 + (
      c1 + 1 + ((2 * (14 * b3 + 5) + 2) + 1 + (
      c2 + 1 + (
      (2 * (14 * b4 + 5) + 2) + 1 + (
      c3 + 1 + (
      (2 * (14 * b5 + 5) + 2) + 1 + (
      c4 + 1 + (
      (2 * nc + 2)))))))))))))) ≤ Y ^ 147 := by
  have hb : 81 * Y ^ 145 ≤ Y ^ (145 + 2) := ybig hY 145 81 2 (by norm_num) le_rfl
  have hp := ypos hY 145
  show _ ≤ Y ^ (145 + 2)
  linarith

theorem accMass_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) :
    PCPSerializerMass.mass (accOf (WLv l) (P3v l) (l.count true)) ≤ Y ^ 10 := by
  have hY : 9 ≤ Y := by omega
  have hk : l.count true ≤ l.length := List.count_le_length
  have k1 : l.count true ≤ Y ^ 1 := by rw [pow_one]; omega
  have hacc := acc_le l (l.count true) hk
  rw [← hYn] at hacc
  have h9 : 600 * Y ^ 5 + 401 ≤ Y ^ (5 + 4) := ylin hY (le_refl (Y ^ 5)) 600 401 4 (by norm_num)
  rw [mass_eq]
  exact hacc.trans (ym k1 h9)

theorem gs_mass_y (k : ℕ) (hk : 3 * k ≤ Y) : PCPSerializerMass.mass (gsOf k) ≤ Y ^ 1 := by
  rw [mass_gs, pow_one]
  have := bits_len_le k
  omega

theorem encodeNat_y (hY : 9 ≤ Y) (k : ℕ) (hk : 3 * k ≤ Y) : (CanonicalBinary.encodeNat k).bits.length ≤ Y ^ 11 := by
  rw [← code_gsOf]
  exact serBits_y hY _ 1 (gs_mass_y k hk)

/-- **The suffix within `Y^147`**, for any top and tag codes within `Y^20`. -/
theorem suf_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) (topv tagv : ℕ)
    (htv : topv.bits.length ≤ Y ^ 20) (htg : tagv.bits.length ≤ Y ^ 20) :
    sufCost (accOf (WLv l) (P3v l) (l.count true)) (l.count true) topv tagv ≤ Y ^ 147 := by
  have hY : 9 ≤ Y := by omega
  have hk : l.count true ≤ l.length := List.count_le_length
  have k3 : 3 * l.count true ≤ Y := by omega
  have hm := accMass_y l Y hYn
  have cb : (PCPTraversal.code (accOf (WLv l) (P3v l) (l.count true))).bits.length ≤ Y ^ 56 :=
    serBits_y hY _ 10 hm
  have eb := encodeNat_y hY (l.count true) k3
  have t1 : (cons topv 0).bits.length ≤ Y ^ 23 := consBits_y hY topv 0 20 htv (zero_bits_y 20)
  have t2 : (cons (PCPTraversal.code (accOf (WLv l) (P3v l) (l.count true))) (cons topv 0)).bits.length ≤ Y ^ 59 :=
    consBits_y hY _ _ 56 cb (yle hY (by norm_num) t1)
  have t3 : (cons (CanonicalBinary.encodeNat (l.count true))
      (cons (PCPTraversal.code (accOf (WLv l) (P3v l) (l.count true))) (cons topv 0))).bits.length ≤ Y ^ 62 :=
    consBits_y hY _ _ 59 (yle hY (by norm_num) eb) t2
  have t4 : (sufCode (accOf (WLv l) (P3v l) (l.count true)) (l.count true) topv tagv).bits.length ≤ Y ^ 65 :=
    consBits_y hY _ _ 62 (yle hY (by norm_num) htg) t3
  have nc : 2 * natCost (sufCode (accOf (WLv l) (P3v l) (l.count true)) (l.count true) topv tagv) + 2 ≤ Y ^ 145 := by
    unfold natCost
    have := yle hY (show 65 + 3 ≤ 145 by norm_num) (ylin hY t4 84 82 3 (by norm_num))
    omega
  exact sufSum hY _ _ _ _ _ _ _ _ _ _ _ _
    (ser_y hY _ 10 hm)
    (yle hY (show _ ≤ 145 by norm_num) (cp_y hY _ 56 cb))
    (yle hY (show _ ≤ 145 by norm_num) (ser_y hY (gsOf (l.count true)) 1 (gs_mass_y _ k3)))
    (yle hY (show _ ≤ 145 by norm_num) (cp_y hY _ 11 eb))
    (yle hY (show _ ≤ 145 by norm_num) (consB_y hY topv 0 20 htv (zero_bits_y 20)))
    (yle hY (show _ ≤ 145 by norm_num) (cp_y hY _ 23 t1))
    (yle hY (show _ ≤ 145 by norm_num) (consB_y hY _ _ 56 cb (yle hY (by norm_num) t1)))
    (yle hY (show _ ≤ 145 by norm_num) (cp_y hY _ 59 t2))
    (yle hY (show _ ≤ 145 by norm_num) (consB_y hY _ _ 59 (yle hY (by norm_num) eb) t2))
    (yle hY (show _ ≤ 145 by norm_num) (cp_y hY _ 62 t3))
    (yle hY (show _ ≤ 145 by norm_num) (consB_y hY _ _ 62 (yle hY (by norm_num) htg) t3))
    nc

/-! ## The core -/

/-- **The parity writer's core within `Y^148`**, `Y = 9 n + 9`, for a top within `Y^44` writing codes within `Y^20`. -/
theorem core_y (l : List Bool) (Y : ℕ) (hYn : Y = 9 * l.length + 9) (ctop topv tagv : ℕ) (hct : ctop ≤ Y ^ 44)
    (htv : topv.bits.length ≤ Y ^ 20) (htg : tagv.bits.length ≤ Y ^ 20) :
    CWParPre.preCost l + 1 + (CWParLoop.loopCost (l.count true) l.length CWParFit.CP (CWParFit.cwP l.length) + 1 +
      (ctop + 1 + sufCost (accOf (WLv l) (P3v l) (l.count true)) (l.count true) topv tagv)) ≤ Y ^ 148 := by
  have hY : 9 ≤ Y := by omega
  have a1 := yle hY (show 39 ≤ 147 by norm_num) (pre_y l Y hYn)
  have a2 := yle hY (show 64 ≤ 147 by norm_num) (loop_y l Y hYn)
  have a3 := yle hY (show 44 ≤ 147 by norm_num) hct
  have a4 := suf_y l Y hYn topv tagv htv htg
  have hb : 9 * Y ^ 147 ≤ Y ^ (147 + 1) := ybig hY 147 9 1 (by norm_num) le_rfl
  have hp := ypos hY 147
  show _ ≤ Y ^ (147 + 1)
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.CWParTimeB
