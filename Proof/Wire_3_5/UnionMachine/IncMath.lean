import Proof.Wire_3_5.Primitive.Writers.ParseNat

/-! # C6 front, the C1 dock: `intWord (z+1)` from `intWord z`, the bit arithmetic

C1's request word `selWord` carries every gate as `intWord`s of its weights and of its threshold `θ`
(`Plan.selWord`), while base's decoders give a bottom gate as its native word, whose last field is `intWord (θ − 1)`
(`thresholdWord (nonStrictAsStrict g)`, `TabRef.tabGW_eq`). The writer adds `1` to that field bit by bit (a
threshold is a number of polynomially many BITS, never read into a unary register). This module fixes the words:
* `bv` (the LSB-first value), `incC` (carry `c` through the bits), `decC` (borrow `c`), their value laws;
* **`natWord_succ`**: `natWord (m+1)` is the `incC` of `natWord m`'s bits with one more bit iff they are all ones;
* **`natWord_pred`**: `natWord (m−1)` (`m ≥ 1`) is the `decC` of `natWord m`'s bits, one bit shorter iff `m` is a power
  of two at least `2`;
* **`intWord_succ_nonneg`**, **`intWord_succ_neg`**.

Paper quantity: the gate threshold `θ` of C1's request (`star:selection`'s populations, P3:1326-1330). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.IncMath
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WilliamsPublishedForm

/-! ## Values of bit lists -/

/-- The LSB-first value of a bit list. -/
def bv : List Bool → ℕ
  | [] => 0
  | b :: t => b.toNat + 2 * bv t

theorem bv_lt : ∀ l : List Bool, bv l < 2 ^ l.length
  | [] => by simp [bv]
  | b :: t => by
    have := bv_lt t
    have hb : b.toNat ≤ 1 := Bool.toNat_le b
    simp only [bv, List.length_cons, pow_succ]
    omega

theorem fwb_succ (w v : ℕ) : fixedWidthNatBits (w + 1) v = v.testBit 0 :: fixedWidthNatBits w (v / 2) := by
  unfold fixedWidthNatBits
  rw [List.ofFn_succ]
  congr 1
  exact List.ofFn_inj.mpr (funext fun i => by simp [Nat.testBit_div_two])

theorem testBit_zero_toNat (v : ℕ) : (v.testBit 0).toNat = v % 2 := by
  rw [Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

theorem bv_fwb : ∀ (w v : ℕ), bv (fixedWidthNatBits w v) = v % 2 ^ w
  | 0, v => by simp [fixedWidthNatBits, bv, Nat.mod_one]
  | w + 1, v => by
    rw [fwb_succ, bv, bv_fwb w (v / 2), testBit_zero_toNat, pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mod_mul]

theorem fwb_length (w v : ℕ) : (fixedWidthNatBits w v).length = w := by simp [fixedWidthNatBits]

/-- **A bit list is the fixed-width bits of its value.** -/
theorem eq_fwb : ∀ (l : List Bool), l = fixedWidthNatBits l.length (bv l)
  | [] => by simp [fixedWidthNatBits]
  | b :: t => by
    have ih := eq_fwb t
    rw [List.length_cons, fwb_succ]
    have h1 : (bv (b :: t)).testBit 0 = b := by
      rw [Nat.testBit_zero]; simp only [bv]; cases b <;> simp
    have h2 : bv (b :: t) / 2 = bv t := by simp only [bv]; cases b <;> simp <;> omega
    rw [h1, h2, ← ih]

/-! ## Carry and borrow -/

/-- Add the carry `c` bit by bit: the new bits and the carry out. -/
def incC : Bool → List Bool → List Bool × Bool
  | c, [] => ([], c)
  | c, b :: t => ((xor b c) :: (incC (c && b) t).1, (incC (c && b) t).2)

/-- Subtract the borrow `c` bit by bit: the new bits and the borrow out. -/
def decC : Bool → List Bool → List Bool × Bool
  | c, [] => ([], c)
  | c, b :: t => ((xor b c) :: (decC (c && !b) t).1, (decC (c && !b) t).2)

theorem incC_length : ∀ (c : Bool) (l : List Bool), (incC c l).1.length = l.length
  | _, [] => rfl
  | c, b :: t => by simp [incC, incC_length (c && b) t]

theorem decC_length : ∀ (c : Bool) (l : List Bool), (decC c l).1.length = l.length
  | _, [] => rfl
  | c, b :: t => by simp [decC, decC_length (c && !b) t]

theorem incC_val : ∀ (c : Bool) (l : List Bool),
    bv (incC c l).1 + 2 ^ l.length * (incC c l).2.toNat = bv l + c.toNat
  | c, [] => by simp [incC, bv]
  | c, b :: t => by
    have ih := incC_val (c && b) t
    simp only [incC, bv, List.length_cons, pow_succ]
    cases b <;> cases c <;> simp at ih ⊢ <;> nlinarith

theorem decC_val : ∀ (c : Bool) (l : List Bool),
    bv (decC c l).1 + c.toNat = bv l + 2 ^ l.length * (decC c l).2.toNat
  | c, [] => by simp [decC, bv]
  | c, b :: t => by
    have ih := decC_val (c && !b) t
    simp only [decC, bv, List.length_cons, pow_succ]
    cases b <;> cases c <;> simp at ih ⊢ <;> nlinarith

/-! ## `natWord` of a successor and of a predecessor -/

theorem natWord_eq' (m : ℕ) : natWord m =
    List.replicate (natBitLength m) true ++ false :: fixedWidthNatBits (natBitLength m) m := rfl

theorem lt_pow_nbl (m : ℕ) : m < 2 ^ natBitLength m := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) m

theorem pow_nbl_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ (natBitLength m - 1) ≤ m := by
  unfold natBitLength
  rw [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (by omega)

theorem nbl_eq (m k : ℕ) (h1 : 2 ^ k ≤ m) (h2 : m < 2 ^ (k + 1)) : natBitLength m = k + 1 := by
  unfold natBitLength
  rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

theorem nbl_pos (m : ℕ) : 1 ≤ natBitLength m := by unfold natBitLength; omega

/-- **The successor's word**: the carry of `1` through `natWord m`'s bits, and one more bit iff the carry leaves. -/
theorem natWord_succ (m : ℕ) :
    natWord (m + 1) = List.replicate (natBitLength m + (incC true (fixedWidthNatBits (natBitLength m) m)).2.toNat)
      true ++ false :: ((incC true (fixedWidthNatBits (natBitLength m) m)).1 ++
        (if (incC true (fixedWidthNatBits (natBitLength m) m)).2 then [true] else [])) := by
  set w := natBitLength m with hw
  set bs := fixedWidthNatBits w m with hbs
  have hlen : bs.length = w := fwb_length w m
  have hlt := lt_pow_nbl m
  rw [← hw] at hlt
  have hbv : bv bs = m := by rw [hbs, bv_fwb, Nat.mod_eq_of_lt hlt]
  have hv := incC_val true bs
  rw [hlen, hbv] at hv
  have hl1 := incC_length true bs
  rw [hlen] at hl1
  have hw1 : 1 ≤ w := nbl_pos m
  set out := (incC true bs).1 ++ (if (incC true bs).2 then [true] else []) with hout
  have hol : out.length = w + (incC true bs).2.toNat := by
    rw [hout]; cases hc : (incC true bs).2 <;> simp [hl1]
  have hob : bv out = m + 1 := by
    rw [hout]
    have hb := bv_lt (incC true bs).1
    rw [hl1] at hb
    cases hc : (incC true bs).2
    · simp [hc] at hv ⊢; omega
    · simp only [if_true]
      have happ : ∀ l : List Bool, bv (l ++ [true]) = bv l + 2 ^ l.length := by
        intro l
        induction l with
        | nil => simp [bv]
        | cons b t ih => simp only [List.cons_append, bv, ih, List.length_cons, pow_succ]; ring
      rw [happ, hl1]
      simp [hc] at hv; omega
  have hnbl : natBitLength (m + 1) = w + (incC true bs).2.toNat := by
    cases hc : (incC true bs).2
    · simp only [hc, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.add_zero] at hv ⊢
      have hb := bv_lt (incC true bs).1
      rw [hl1] at hb
      have h1 : m + 1 < 2 ^ w := by omega
      have h2 : 2 ^ (w - 1) ≤ m + 1 := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          have : w = 1 := by rw [hw]; rfl
          rw [this]; norm_num
        · have := pow_nbl_le m h0; rw [← hw] at this; omega
      have e := nbl_eq (m + 1) (w - 1) h2 (by rw [show w - 1 + 1 = w by omega]; exact h1)
      omega
    · simp only [hc, Bool.toNat_true, Nat.mul_one] at hv ⊢
      have hb := bv_lt (incC true bs).1
      rw [hl1] at hb
      have h1 : m + 1 = 2 ^ w := by
        have := Nat.lt_or_ge (bv (incC true bs).1) 1
        omega
      exact nbl_eq (m + 1) w (le_of_eq h1.symm) (by rw [h1, pow_succ]; omega)
  have hfw : out = fixedWidthNatBits (natBitLength (m + 1)) (m + 1) := by
    rw [hnbl, ← hol, ← hob]
    exact eq_fwb out
  rw [natWord_eq' (m + 1), hfw, hnbl]

theorem fwb_take (w k v : ℕ) (hk : k ≤ w) : (fixedWidthNatBits w v).take k = fixedWidthNatBits k v := by
  unfold fixedWidthNatBits
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp

/-- The predecessor's bit length: one less exactly at a power of two `≥ 2`. -/
def dropP (m : ℕ) : Bool := decide (2 ≤ natBitLength m ∧ m % 2 ^ (natBitLength m - 1) = 0)

theorem nbl_pred (m : ℕ) (hm : 1 ≤ m) :
    natBitLength (m - 1) = natBitLength m - (dropP m).toNat := by
  set w := natBitLength m with hw
  have hlt := lt_pow_nbl m
  have hge := pow_nbl_le m hm
  rw [← hw] at hlt hge
  have hw1 : 1 ≤ w := nbl_pos m
  unfold dropP
  rw [← hw]
  by_cases h2 : 2 ≤ w
  · by_cases hz : m % 2 ^ (w - 1) = 0
    · have hd : decide (2 ≤ w ∧ m % 2 ^ (w - 1) = 0) = true := by simp [h2, hz]
      rw [hd]
      -- `m = 2^(w-1)`
      have hm2 : m = 2 ^ (w - 1) := by
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hz
        have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
          rw [← pow_succ']; congr 1 <;> omega
        have hk1 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h; simp at hk; omega
          · exact h
        have hk2 : k < 2 := by
          by_contra hc
          have : 2 ^ (w - 1) * 2 ≤ 2 ^ (w - 1) * k := Nat.mul_le_mul_left _ (by omega)
          omega
        have : k = 1 := by omega
        subst this; simpa using hk
      have e := nbl_eq (m - 1) (w - 2) (by
          rw [hm2]
          have : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by rw [← pow_succ']; congr 1 <;> omega
          have h1 := Nat.one_le_two_pow (n := w - 2)
          omega) (by
          rw [hm2, show w - 2 + 1 = w - 1 by omega]
          have := Nat.one_le_two_pow (n := w - 1)
          omega)
      simp only [Bool.toNat_true]
      omega
    · have hd : decide (2 ≤ w ∧ m % 2 ^ (w - 1) = 0) = false := by simp [hz]
      rw [hd]
      have hgt : 2 ^ (w - 1) < m := by
        rcases Nat.lt_or_ge (2 ^ (w - 1)) m with h | h
        · exact h
        · have : m = 2 ^ (w - 1) := le_antisymm h hge
          rw [this, Nat.mod_self] at hz; exact absurd rfl hz
      have e := nbl_eq (m - 1) (w - 1) (by omega) (by rw [show w - 1 + 1 = w by omega]; omega)
      simp only [Bool.toNat_false]
      omega
  · have hd : decide (2 ≤ w ∧ m % 2 ^ (w - 1) = 0) = false := by simp [h2]
    rw [hd]
    have hw1' : w = 1 := by omega
    rw [hw1'] at hlt
    have : m = 1 := by norm_num at hlt; omega
    subst this
    simp only [Bool.toNat_false, Nat.sub_zero]
    rw [hw1']; rfl

/-- **The predecessor's word** (`m ≥ 1`): the borrow of `1` through `natWord m`'s bits, cut to the predecessor's
bit length. -/
theorem natWord_pred (m : ℕ) (hm : 1 ≤ m) :
    natWord (m - 1) = List.replicate (natBitLength m - (dropP m).toNat) true ++
      false :: (decC true (fixedWidthNatBits (natBitLength m) m)).1.take (natBitLength m - (dropP m).toNat) := by
  set w := natBitLength m with hw
  set bs := fixedWidthNatBits w m with hbs
  have hlen : bs.length = w := fwb_length w m
  have hlt := lt_pow_nbl m
  rw [← hw] at hlt
  have hbv : bv bs = m := by rw [hbs, bv_fwb, Nat.mod_eq_of_lt hlt]
  have hv := decC_val true bs
  rw [hlen, hbv] at hv
  have hl1 := decC_length true bs
  rw [hlen] at hl1
  have hb := bv_lt (decC true bs).1
  rw [hl1] at hb
  have hbo : (decC true bs).2 = false := by
    cases hc : (decC true bs).2
    · rfl
    · simp [hc] at hv; omega
  rw [hbo] at hv
  simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
  have hr : (decC true bs).1 = fixedWidthNatBits w (m - 1) := by
    have := eq_fwb (decC true bs).1
    rw [hl1] at this
    rw [this]; congr 1; omega
  have hp := nbl_pred m hm
  rw [← hw] at hp
  rw [natWord_eq' (m - 1), hp, hr, fwb_take _ _ _ (by omega)]

theorem intWord_eq (z : ℤ) : intWord z = decide (z < 0) :: natWord z.natAbs := rfl

/-- `z ≥ 0`: the successor's integer word. -/
theorem intWord_succ_nonneg (z : ℤ) (hz : 0 ≤ z) : intWord (z + 1) = false :: natWord (z.natAbs + 1) := by
  rw [intWord_eq]
  have h1 : ¬ (z + 1 < 0) := by omega
  have h2 : (z + 1).natAbs = z.natAbs + 1 := by omega
  rw [h2]; simp [h1]

/-- `z < 0`: the successor's integer word (negative iff `|z| ≥ 2`). -/
theorem intWord_succ_neg (z : ℤ) (hz : z < 0) :
    intWord (z + 1) = decide (2 ≤ z.natAbs) :: natWord (z.natAbs - 1) := by
  rw [intWord_eq]
  have h2 : (z + 1).natAbs = z.natAbs - 1 := by omega
  have h3 : decide (z + 1 < 0) = decide (2 ≤ z.natAbs) := by
    apply decide_eq_decide.mpr; omega
  rw [h2, h3]

end NearCubicWires.WireExponent3_5.UnionMachine.IncMath
