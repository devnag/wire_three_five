import Proof.Wire_3_5.Primitive.SeedFix.HbStep

/-! # C4.Hb, machine part 15: the odometer's arithmetic (`filt:soft`, P3:2253-2290)

The machine's odometer enumerates the cells `c < N²·nE·|pops|·(J+1)·2^{2t(1+ℓ₀)}` of `hashTermsM` in mixed radix: the
binary word `CTR` (radix `2^{2t(1+ℓ₀)}`, the signs then the positions, low bit first), then the level `λ`, the
population, the aux seed and the star row. One step of the machine (`binSucc`, `odoStep`) is `c ↦ c + 1`
(**`binSucc_binary`**, **`digit_succ`**); the loop's bit clears exactly after the last cell (**`top_succ`**).

Paper quantity of the main type: the cell `(q, e, p, λ, ι, γ)` of counter value `c` (`HbX.qc`, …, `HbX.ιs`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

section Bin

theorem binary_split' (a b n : ℕ) : binary (a + b) n = binary a n ++ binary b (n / 2 ^ a) := by
  induction a generalizing n with
  | zero => simp [SignedSortKey.binary]
  | succ a ih =>
    rw [Nat.succ_add]
    show (n % 2 == 1) :: binary (a + b) (n / 2) = (n % 2 == 1) :: binary a (n / 2) ++ binary b (n / 2 ^ (a + 1))
    rw [ih, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 2]
    rfl

theorem binary_mod' : ∀ (w n : ℕ), binary w (n % 2 ^ w) = binary w n
  | 0, _ => rfl
  | w + 1, n => by
    show ((n % 2 ^ (w + 1)) % 2 == 1) :: binary w ((n % 2 ^ (w + 1)) / 2) = (n % 2 == 1) :: binary w (n / 2)
    have h1 : n % 2 ^ (w + 1) % 2 = n % 2 := by
      rw [pow_succ, Nat.mod_mul_left_mod]
    have h2 : n % 2 ^ (w + 1) / 2 = (n / 2) % 2 ^ w := by
      rw [pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
    rw [h1, h2, binary_mod' w (n / 2)]

theorem binSucc_false (w : List Bool) : binSucc (false :: w) = true :: w := by
  simp [binSucc, lead]

theorem binSucc_true (w : List Bool) : binSucc (true :: w) = false :: binSucc w := by
  unfold binSucc
  simp only [lead, List.length_cons]
  by_cases h : lead w < w.length
  · rw [if_pos (by omega), if_pos h]; simp [List.replicate_succ]
  · rw [if_neg (by omega), if_neg h]; simp [List.replicate_succ]

theorem lead_true (w : List Bool) : lead (true :: w) = lead w + 1 := rfl

/-- **The binary successor** is `+1` modulo `2^L`, and the word is all ones exactly when `+1` carries out. -/
theorem binSucc_binary : ∀ (L m : ℕ), m < 2 ^ L →
    binSucc (binary L m) = binary L ((m + 1) % 2 ^ L) ∧ (lead (binary L m) < L ↔ m + 1 < 2 ^ L)
  | 0, m, h => by
    have : m = 0 := by simpa using h
    subst this
    simp [binSucc, lead, SignedSortKey.binary]
  | L + 1, m, h => by
    have hm2 : m / 2 < 2 ^ L := by rw [pow_succ] at h; omega
    obtain ⟨ih1, ih2⟩ := binSucc_binary L (m / 2) hm2
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · have e1 : (m % 2 == 1) = false := by simp [h0]
      have e2 : ((m + 1) % 2 ^ (L + 1)) = m + 1 := Nat.mod_eq_of_lt (by rw [pow_succ]; omega)
      have e3 : (m + 1) % 2 = 1 := by omega
      have e4 : (m + 1) / 2 = m / 2 := by omega
      show binSucc ((m % 2 == 1) :: binary L (m / 2)) = binary (L + 1) ((m + 1) % 2 ^ (L + 1)) ∧
        (lead ((m % 2 == 1) :: binary L (m / 2)) < L + 1 ↔ m + 1 < 2 ^ (L + 1))
      rw [e1, binSucc_false, e2]
      refine ⟨?_, ?_⟩
      · show true :: binary L (m / 2) = ((m + 1) % 2 == 1) :: binary L ((m + 1) / 2)
        rw [e3, e4]; rfl
      · simp only [lead]; rw [pow_succ]; constructor <;> intro _ <;> omega
    · have e1 : (m % 2 == 1) = true := by simp [h1]
      show binSucc ((m % 2 == 1) :: binary L (m / 2)) = binary (L + 1) ((m + 1) % 2 ^ (L + 1)) ∧
        (lead ((m % 2 == 1) :: binary L (m / 2)) < L + 1 ↔ m + 1 < 2 ^ (L + 1))
      rw [e1, binSucc_true, lead_true, ih1]
      refine ⟨?_, ?_⟩
      · show false :: binary L ((m / 2 + 1) % 2 ^ L) = ((m + 1) % 2 ^ (L + 1) % 2 == 1) ::
          binary L ((m + 1) % 2 ^ (L + 1) / 2)
        have f1 : (m + 1) % 2 ^ (L + 1) % 2 = 0 := by
          rw [pow_succ, Nat.mod_mul_left_mod]; omega
        have f2 : (m + 1) % 2 ^ (L + 1) / 2 = (m / 2 + 1) % 2 ^ L := by
          rw [pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self]
          congr 1; omega
        rw [f1, f2]; rfl
      · rw [pow_succ]; constructor
        · intro hl; have := ih2.mp (by omega); omega
        · intro hl; have := ih2.mpr (by omega); omega

end Bin

section Digit

/-- **One mixed-radix digit step**: the digit of `x + c` and the carry into the next digit. -/
theorem digit_succ (x c R : ℕ) (hR : 0 < R) (hc : c ≤ 1) :
    (x + c) % R = (dstep c (x % R) R).1 ∧ (x + c) / R = x / R + (dstep c (x % R) R).2 := by
  have hd := Nat.div_add_mod x R
  have hlt := Nat.mod_lt x hR
  set q := x / R
  set r := x % R
  unfold dstep
  by_cases h0 : c = 0
  · subst h0; simp; exact ⟨rfl, rfl⟩
  · have h1 : c = 1 := by omega
    subst h1
    simp only [one_ne_zero, if_false]
    by_cases h : r + 1 < R
    · rw [if_pos h]
      have e : x + 1 = r + 1 + R * q := by omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt h]
      simp
    · rw [if_neg h]
      have e : x + 1 = R * (q + 1) := by rw [Nat.mul_add]; omega
      rw [e, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hR]
      simp

end Digit

end NearCubicWires.WireExponent3_5.PrimT.HbM
