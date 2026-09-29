import Mathlib

/-!
# Local finite algebra for the threshold AND-four supplier

This file proves representation identities used by Appendices A--B.  It does
not formalize the asymptotic rectangular product, expander estimate, or prime
density theorem.  There are no declarations by `postulate` and no incomplete
proofs.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.ThresholdCompiler

def bitInt (b : Bool) : ℤ := if b then 1 else 0

theorem trueEquationPassesEveryModulus (modulus : ℤ) :
    (0 : ℤ) % modulus = 0 := by
  simp

theorem boundedMultipleIsZero (base digit : ℤ)
    (hbase : 0 < base) (hlower : -base < digit) (hupper : digit < base)
    (hdiv : base ∣ digit) : digit = 0 := by
  rcases hdiv with ⟨multiple, rfl⟩
  rcases lt_trichotomy multiple 0 with hneg | hzero | hpos
  · have hmultiple : multiple ≤ -1 := by omega
    have : base * multiple ≤ -base := by nlinarith
    omega
  · simp [hzero]
  · have hmultiple : 1 ≤ multiple := by omega
    have : base ≤ base * multiple := by nlinarith
    omega

/-- The full occurrence lift, indexed so `j = 0` is the singleton layer. -/
def binLiftFull (t : ℕ) : ℤ :=
  ∑ j ∈ range t, (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)

/-- The occurrence lift truncated after subset size `q`. -/
def binLift (q t : ℕ) : ℤ :=
  ∑ j ∈ range (min q t), (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)

theorem twoMulBinLiftFull (t : ℕ) :
    2 * binLiftFull t = 1 - (-1 : ℤ) ^ t := by
  have hbinom :
      (-1 : ℤ) ^ t =
        ∑ m ∈ range (t + 1), (-2 : ℤ) ^ m * (t.choose m : ℤ) := by
    simpa using (add_pow (-2 : ℤ) 1 t)
  rw [sum_range_succ'] at hbinom
  have htail :
      (∑ j ∈ range t,
          (-2 : ℤ) ^ (j + 1) * (t.choose (j + 1) : ℤ)) =
        -2 * binLiftFull t := by
    simp only [binLiftFull, pow_succ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [htail] at hbinom
  norm_num at hbinom ⊢
  omega

theorem binLiftFullEven (t : ℕ) (ht : Even t) : binLiftFull t = 0 := by
  have h := twoMulBinLiftFull t
  have hpow : (-1 : ℤ) ^ t = 1 := ht.neg_one_pow
  rw [hpow] at h
  omega

theorem binLiftFullOdd (t : ℕ) (ht : Odd t) : binLiftFull t = 1 := by
  have h := twoMulBinLiftFull t
  have hpow : (-1 : ℤ) ^ t = -1 := ht.neg_one_pow
  rw [hpow] at h
  omega

theorem omittedBinLiftTermModEqZero
    (q j t : ℕ) (h : q ≤ j) :
    (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ) ≡ 0 [ZMOD (2 : ℤ) ^ q] := by
  apply Int.modEq_zero_iff_dvd.mpr
  have hp : (2 : ℤ) ^ q ∣ (2 : ℤ) ^ j := pow_dvd_pow 2 h
  have hn : (2 : ℤ) ^ q ∣ (-2 : ℤ) ^ j := by
    rw [show (-2 : ℤ) = (-1 : ℤ) * 2 by norm_num, mul_pow]
    exact dvd_mul_of_dvd_right hp _
  exact dvd_mul_of_dvd_left hn _

theorem binLiftModEqFull (q t : ℕ) :
    binLift q t ≡ binLiftFull t [ZMOD (2 : ℤ) ^ q] := by
  rcases le_total q t with hqt | htq
  · have hadd : q + (t - q) = t := Nat.add_sub_of_le hqt
    have htail :
        (∑ i ∈ range (t - q),
            (-2 : ℤ) ^ (q + i) * (t.choose (q + i + 1) : ℤ)) ≡
          0 [ZMOD (2 : ℤ) ^ q] := by
      simpa using Int.ModEq.sum (s := range (t - q)) (fun i _ =>
        omittedBinLiftTermModEqZero q (q + i) t (Nat.le_add_right q i))
    unfold binLift binLiftFull
    rw [Nat.min_eq_left hqt]
    have hsplit := sum_range_add
      (fun j => (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)) q (t - q)
    rw [hadd] at hsplit
    rw [hsplit]
    have hhead :
        (∑ j ∈ range q,
            (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ)) ≡
          (∑ j ∈ range q,
            (-2 : ℤ) ^ j * (t.choose (j + 1) : ℤ))
          [ZMOD (2 : ℤ) ^ q] := Int.ModEq.rfl
    simpa using (hhead.add htail).symm
  · unfold binLift binLiftFull
    rw [Nat.min_eq_right htq]

theorem binLiftModEqParity (q t : ℕ) :
    binLift q t ≡ ((t % 2 : ℕ) : ℤ) [ZMOD (2 : ℤ) ^ q] := by
  rcases Nat.even_or_odd t with ht | ht
  · have hfull := binLiftModEqFull q t
    rw [binLiftFullEven t ht] at hfull
    have hmod : t % 2 = 0 := Nat.even_iff.mp ht
    simpa [hmod] using hfull
  · have hfull := binLiftModEqFull q t
    rw [binLiftFullOdd t ht] at hfull
    have hmod : t % 2 = 1 := Nat.odd_iff.mp ht
    simpa [hmod] using hfull

/-! ## The executable corrected first-crossing compiler

The declarations below are the kernel-checked counterpart of
`reference_compiler.erratum_safe_disjoint_children`.  In particular, the
compiler traverses bit levels and variables in descending order, starts from
the explicit zero sentinel, permits a zero quotient, and expands complemented
literals only after constructing the nonnegative crossing equation.
-/

namespace ExactEquation

end ExactEquation

@[simp] theorem bitInt_eq_toNat (b : Bool) : bitInt b = b.toNat := by
  cases b <;> rfl

end NearCubicWires.ThresholdCompiler
