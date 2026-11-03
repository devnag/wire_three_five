import Proof.Wire_3_5.UnionMachine.FrontCapsBase
import Proof.Wire_3_5.UnionMachine.FrontSemRunBase

/-! # C6 front, the semantic core (8): the width is logarithmic (P3:3632-3655)

The native width `q(N) = ⌈log₂ N^{k+2}⌉ + A_pad·⌈log₂(⌈log₂ N^{k+2}⌉+2)⌉ + A_pad` is at most `K·L(N)`
(**`nw_le_Lq`**, `L(N) = ⌈log₂(N+2)⌉`), so every fixed polynomial of `q(N)` is eventually at most `N`
(**`polyq_le`**): the front's polynomial-in-`q` sizes fit its `N`-sized input tapes.

Paper quantity: the native width `q(N)` against the input length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEv
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Ledger Filter

/-- The width's logarithmic constant. -/
def Kn (kclk Apad : ℕ) : ℕ := (kclk + 2) * (1 + Apad) + 3 * Apad

theorem clog_pow_le (N k : ℕ) : Nat.clog 2 (N ^ k) ≤ k * Nat.clog 2 N := by
  apply Nat.clog_le_of_le_pow
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) N) k

theorem clog_le_self (x : ℕ) : Nat.clog 2 x ≤ x :=
  Nat.clog_le_of_le_pow ((Nat.lt_two_pow_self).le)

/-- **The width is logarithmic.** -/
theorem nw_le_Lq (kclk Apad N : ℕ) : nativeWidth kclk Apad N ≤ Kn kclk Apad * Lq N := by
  have hL := Lq_pos N
  have h1 : Nat.clog 2 (N ^ (kclk + 2)) ≤ (kclk + 2) * Lq N :=
    (clog_pow_le N (kclk + 2)).trans (Nat.mul_le_mul_left _ (Nat.clog_mono_right 2 (by omega)))
  have h2 : Nat.clog 2 (Nat.clog 2 (N ^ (kclk + 2)) + 2) ≤ Nat.clog 2 (N ^ (kclk + 2)) + 2 := clog_le_self _
  have h3 := Nat.mul_le_mul_left Apad h2
  unfold nativeWidth Kn
  have e1 : ((kclk + 2) * (1 + Apad) + 3 * Apad) * Lq N =
      (kclk + 2) * Lq N + Apad * ((kclk + 2) * Lq N) + 3 * Apad * Lq N := by ring
  have e2 : 3 * Apad ≤ 3 * Apad * Lq N := Nat.le_mul_of_pos_right _ hL
  have e3 : Apad * (Nat.clog 2 (N ^ (kclk + 2)) + 2) ≤ Apad * ((kclk + 2) * Lq N) + 2 * Apad := by
    have := Nat.mul_le_mul_left Apad h1
    rw [Nat.mul_add]; omega
  omega

/-- **Every fixed polynomial of the width is eventually at most `N`.** -/
theorem polyq_le (kclk Apad c d : ℕ) : ∀ᶠ N : ℕ in atTop, c * (nativeWidth kclk Apad N + 1) ^ d ≤ N := by
  filter_upwards [eventually_mul_Lq_pow_le (c * (Kn kclk Apad + 1) ^ d) d] with N hN
  have hL := Lq_pos N
  have h1 : nativeWidth kclk Apad N + 1 ≤ (Kn kclk Apad + 1) * Lq N := by
    have := nw_le_Lq kclk Apad N
    rw [Nat.add_mul, one_mul]; omega
  calc c * (nativeWidth kclk Apad N + 1) ^ d ≤ c * ((Kn kclk Apad + 1) * Lq N) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = c * (Kn kclk Apad + 1) ^ d * Lq N ^ d := by rw [mul_pow]; ring
    _ ≤ N := hN

theorem nbl_le_Lq (q : ℕ) : natBitLength q ≤ Lq q := by
  unfold natBitLength Lq
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h; simp; exact Nat.clog_pos (by norm_num) (by norm_num)
  · have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
    have h2 : q + 2 ≤ 2 ^ Nat.clog 2 (q + 2) := Nat.le_pow_clog (by norm_num) _
    have h3 : 2 ^ Nat.log 2 q < 2 ^ Nat.clog 2 (q + 2) := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
    omega

theorem nbl_le_self (q : ℕ) : natBitLength q ≤ q + 1 := by
  unfold natBitLength
  have : Nat.log 2 q ≤ q := (Nat.log_le_self 2 q)
  omega

/-- **The width's bit length is a small fraction of it**, eventually. -/
theorem eventually_nbl (c : ℕ) : ∀ᶠ q : ℕ in atTop, c * natBitLength q ≤ q := by
  filter_upwards [eventually_mul_Lq_pow_le c 1] with q hq
  have := nbl_le_Lq q
  rw [pow_one] at hq
  exact (Nat.mul_le_mul_left c this).trans hq

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemEv
