import Proof.Wire_3_5.UnionMachine.CWParSem

/-! # C6 front, U5, the code writers: sizes of the parity writer's codes

The parity writer (P3:3092-3094) must run within a fixed polynomial of its input (the interface's `K·(n+1)^d`); its
loop must fit a capacity computed from `1^q`. This module bounds the bit lengths of the codes it builds and the
budgets of base's machines it docks, in terms of the bit lengths of their operands:
* `pair_bits`, `cons_bits`: a pair node's and a tagged cons's output width;
* `ser_bits`, `serCost_le`: base's serializer's output width and fuel, by the fields' mass;
* `pairB_le`, `consB_le`: base's pair and tagged-cons fuels, quadratic in their operands' widths.

Paper quantity: none (the writer's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParSize
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.CanonicalBinary
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (cons)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serCost)

theorem pair_bits (a b : ℕ) : (Nat.pair a b).bits.length ≤ 2 * (a.bits.length + b.bits.length + 1) := by
  have h := PCPPair.pair_bound a.bits b.bits
  rw [CanonicalPositiveOutput.nat_bits_value, CanonicalPositiveOutput.nat_bits_value] at h
  have := CanonicalPositiveOutput.nat_bits_length_le _ _ h
  unfold PCPPair.width at this
  exact this

theorem one_bits : (1 : ℕ).bits.length = 1 := by decide

theorem cons_bits (a b : ℕ) : (cons a b).bits.length ≤ 4 * (a.bits.length + b.bits.length) + 8 := by
  unfold cons
  have h1 := pair_bits 1 (Nat.pair a b)
  have h2 := pair_bits a b
  rw [one_bits] at h1
  omega

theorem ser_bits (gs : List (List Bool)) :
    (PCPTraversal.code gs).bits.length ≤ 3 * (PCPSerializerMass.mass gs + 1) ^ 5 :=
  PCPSerializerMass.code_bits gs

theorem mass_eq (gs : List (List Bool)) : PCPSerializerMass.mass gs = (gs.flatMap frame).length := by
  rw [← PCPTraversal.stream_mass, CWCore.stream_eq]

theorem serCost_le (gs : List (List Bool)) :
    serCost gs ≤ 2 * 1000000000000 * (PCPSerializerMass.mass gs + 1) ^ 12 + 6 := by
  unfold serCost PCPTraversal.budget; omega

theorem canB_le (l r : List Bool) :
    PCPPairCanonical.budget l r ≤ 1024 * (l.length + r.length + 1) ^ 2 + 16 * (l.length + r.length + 1) + 10 := by
  have := PCPPairCold.budget_quadratic l r
  unfold PCPPairCanonical.budget PCPPair.width
  omega

/-- **The pair node's fuel**, quadratic in its operands' widths. -/
theorem pairB_le (a b : ℕ) :
    PCPPRequestPair.budget a b ≤ 1100 * (a.bits.length + b.bits.length + 2) ^ 2 := by
  have h := canB_le a.bits b.bits
  unfold PCPPRequestPair.budget
  have hq : a.bits.length + b.bits.length + 1 ≤ (a.bits.length + b.bits.length + 2) ^ 2 := by nlinarith
  have hq' : (a.bits.length + b.bits.length + 1) ^ 2 ≤ (a.bits.length + b.bits.length + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) _
  have h1 : 1 ≤ (a.bits.length + b.bits.length + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The tagged cons's fuel**, quadratic in its operands' widths. -/
theorem consB_le (a b : ℕ) :
    PCPPRequestTaggedCons.budget a b ≤ 6000 * (a.bits.length + b.bits.length + 2) ^ 2 := by
  have h1 := pairB_le a b
  have h2 := canB_le (1 : ℕ).bits (Nat.pair a b).bits
  have h3 := pair_bits a b
  rw [one_bits] at h2
  unfold PCPPRequestTaggedCons.budget
  set s := a.bits.length + b.bits.length with hs
  set p := (Nat.pair a b).bits.length with hp
  have hp2 : 1 + p + 1 ≤ 2 * (s + 2) := by omega
  have hq : (1 + p + 1) ^ 2 ≤ 4 * (s + 2) ^ 2 := by
    calc (1 + p + 1) ^ 2 ≤ (2 * (s + 2)) ^ 2 := Nat.pow_le_pow_left hp2 _
      _ = 4 * (s + 2) ^ 2 := by ring
  have hl : s + 2 ≤ (s + 2) ^ 2 := by nlinarith
  omega

/-! ## The parity writer's sizes -/

open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParGen
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (codeB accOf gsOf code_gsOf roundPCost)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (WLv SBv P3v wlGs sbGs wlF_gs)

theorem bits_len_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact (Nat.size_le).mpr (Nat.lt_two_pow_self)

theorem frame_len (w : List Bool) : (frame w).length = 2 * w.length + 1 := by
  rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.frame_eq_frameP]; simp

theorem wlF_len : ∀ l : List Bool, (wlF l).length ≤ 9 * l.length
  | [] => by simp [wlF]
  | b :: l => by
    rw [wlF_cons, List.length_append, frame_len]
    have := wlF_len l
    cases b <;> simp [w9] <;> omega

theorem mass_wl (l : List Bool) : PCPSerializerMass.mass (wlGs l) ≤ 9 * l.length := by
  rw [mass_eq, ← wlF_gs]; exact wlF_len l

theorem mass_sb (l : List Bool) : PCPSerializerMass.mass (sbGs l) = 3 * l.length := by
  rw [mass_eq, ← CWParPre.sgl_gs, sgl_length]

theorem mass_gs (m : ℕ) : PCPSerializerMass.mass (gsOf m) = 3 * m.bits.length := by
  rw [mass_eq, ← CWParRound.sgl_gsOf, sgl_length]

theorem sq_le (a b P : ℕ) (hP : 1 ≤ P) : (a * P + b) ^ 2 ≤ (a + b) ^ 2 * P ^ 2 := by
  have h : a * P + b ≤ (a + b) * P := by nlinarith
  calc (a * P + b) ^ 2 ≤ ((a + b) * P) ^ 2 := Nat.pow_le_pow_left h _
    _ = (a + b) ^ 2 * P ^ 2 := by ring

theorem pow_mono (a b e : ℕ) (h : a ≤ b) : a ^ e ≤ b ^ e := Nat.pow_le_pow_left h e

/-- The widths of the parity writer's codes, at `n` inputs, in the unit `P = (9n+9)^5`. -/
structure Widths (l : List Bool) (P : ℕ) : Prop where
  wl : (WLv l).bits.length ≤ 3 * P
  sb : (SBv l).bits.length ≤ 3 * P
  p3 : (P3v l).bits.length ≤ 12 * P + 8

theorem widths (l : List Bool) : Widths l ((9 * l.length + 9) ^ 5) := by
  have hwl := ser_bits (wlGs l)
  have hsb := ser_bits (sbGs l)
  have m1 := mass_wl l
  have m2 := mass_sb l
  have e1 : 3 * (PCPSerializerMass.mass (wlGs l) + 1) ^ 5 ≤ 3 * (9 * l.length + 9) ^ 5 :=
    Nat.mul_le_mul_left _ (pow_mono _ _ _ (by omega))
  have e2 : 3 * (PCPSerializerMass.mass (sbGs l) + 1) ^ 5 ≤ 3 * (9 * l.length + 9) ^ 5 :=
    Nat.mul_le_mul_left _ (pow_mono _ _ _ (by omega))
  refine ⟨hwl.trans e1, hsb.trans e2, ?_⟩
  have hc := cons_bits (SBv l) 0
  have h0 : (0 : ℕ).bits.length = 0 := by decide
  unfold P3v
  have : (SBv l).bits.length ≤ 3 * (9 * l.length + 9) ^ 5 := hsb.trans e2
  omega

/-- The width of the `j`-th bottom's threshold code. -/
theorem E_le (n j : ℕ) (hj : j < n) :
    (CanonicalBinary.encodeNat (j + 1)).bits.length ≤ 3 * (9 * n + 9) ^ 5 := by
  rw [← code_gsOf]
  have h := ser_bits (gsOf (j + 1))
  rw [mass_gs] at h
  have hb := bits_len_le (j + 1)
  exact h.trans (Nat.mul_le_mul_left _ (pow_mono _ _ _ (by omega)))

theorem code_le (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (codeB (WLv l) (P3v l) j).bits.length ≤ 300 * (9 * l.length + 9) ^ 5 + 200 := by
  have w := widths l
  have hE := E_le l.length j hj
  have hθ := pair_bits 0 (CanonicalBinary.encodeNat (j + 1))
  have h0 : (0 : ℕ).bits.length = 0 := by decide
  have hc1 := cons_bits (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) (P3v l)
  have hc2 := cons_bits (WLv l) (cons (Nat.pair 0 (CanonicalBinary.encodeNat (j + 1))) (P3v l))
  unfold codeB
  have := w.wl; have := w.p3
  omega

theorem acc_le (l : List Bool) : ∀ j ≤ l.length,
    ((accOf (WLv l) (P3v l) j).flatMap frame).length ≤ j * (600 * (9 * l.length + 9) ^ 5 + 401)
  | 0, _ => by simp [accOf]
  | j + 1, hj => by
    rw [CWParRound.accOf_succ, List.flatMap_append, List.length_append]
    have ih := acc_le l j (by omega)
    have hc := code_le l j (by omega)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, frame_len]
    rw [Nat.add_mul, one_mul]
    omega

/-! ## The round's fuel -/

theorem sq_bound (x a b P : ℕ) (hP : 1 ≤ P) (hx : x ≤ a * P + b) : x ^ 2 ≤ (a + b) ^ 2 * P ^ 2 :=
  (pow_mono _ _ _ hx).trans (sq_le a b P hP)

/-- **Every round of the bottoms' loop within `3·10^12·(9n+9)^12`.** -/
theorem round_le (l : List Bool) (j : ℕ) (hj : j < l.length) :
    roundPCost (WLv l) (P3v l) j (accOf (WLv l) (P3v l) j) ≤ 3000000000000 * (9 * l.length + 9) ^ 12 := by
  unfold roundPCost CWWords.appendBCost
  set n := l.length with hn
  set P := (9 * n + 9) ^ 5 with hP
  set Q := (9 * n + 9) ^ 12 with hQ
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (by omega)
  have hPP : P ^ 2 ≤ Q := by
    rw [hP, hQ, ← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hPQ : P ≤ Q := by rw [hP, hQ]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
  have hjP : j * P ≤ Q := by
    have h1 : j * P ≤ (9 * n + 9) * P := Nat.mul_le_mul_right _ (by omega)
    have h2 : (9 * n + 9) * P = (9 * n + 9) ^ 6 := by rw [hP]; ring
    have h3 : (9 * n + 9) ^ 6 ≤ Q := by rw [hQ]; exact Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have hnQ : n ≤ Q := by
    have h1 := Nat.le_self_pow (show (12 : ℕ) ≠ 0 by norm_num) (9 * n + 9)
    rw [← hQ] at h1
    omega
  have w := widths l
  rw [← hn, ← hP] at w
  have hE := E_le n j hj
  rw [← hP] at hE
  set E := CanonicalBinary.encodeNat (j + 1) with hEdef
  have hθ := pair_bits 0 E
  have h0 : (0 : ℕ).bits.length = 0 := by decide
  rw [h0] at hθ
  set θ := Nat.pair 0 E with hθdef
  have hc1 := cons_bits θ (P3v l)
  set c1 := cons θ (P3v l) with hc1def
  have hcode := code_le l j hj
  rw [← hn, ← hP] at hcode
  have hacc := acc_le l j hj.le
  rw [← hn, ← hP] at hacc
  have hacc2 : ((accOf (WLv l) (P3v l) j).flatMap frame).length ≤ 600 * Q + 401 * n := by
    have e : j * (600 * P + 401) = 600 * (j * P) + 401 * j := by ring
    omega
  have hbits := bits_len_le j
  -- the serializer on `j + 1`
  have hser := serCost_le (gsOf (j + 1))
  rw [mass_gs] at hser
  have hb1 := bits_len_le (j + 1)
  have hsq : (3 * (j + 1).bits.length + 1) ^ 12 ≤ Q := by rw [hQ]; exact pow_mono _ _ _ (by omega)
  -- the pair node and the two conses
  have b1 : PCPPRequestPair.budget 0 E ≤ 27500 * P ^ 2 := by
    have h := pairB_le 0 E
    rw [h0] at h
    have := sq_bound (0 + E.bits.length + 2) 3 2 P hP1 (by omega)
    omega
  have b2 : PCPPRequestTaggedCons.budget θ (P3v l) ≤ 5400000 * P ^ 2 := by
    have h := consB_le θ (P3v l)
    have := sq_bound (θ.bits.length + (P3v l).bits.length + 2) 18 12 P hP1 (by have := w.p3; omega)
    omega
  have b3 : PCPPRequestTaggedCons.budget (WLv l) c1 ≤ 93750000 * P ^ 2 := by
    have h := consB_le (WLv l) c1
    have := sq_bound ((WLv l).bits.length + c1.bits.length + 2) 75 50 P hP1 (by have := w.wl; have := w.p3; omega)
    omega
  have hcode' := hcode
  have := w.wl; have := w.p3
  generalize P ^ 2 = PP at *
  generalize serCost (gsOf (j + 1)) = sc at *
  generalize (3 * (j + 1).bits.length + 1) ^ 12 = sq12 at *
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.CWParSize
