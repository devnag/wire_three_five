import Outer.Interface

/-!
# O3 (part 4) — the native width `q(N)`

The near-cubic-gates paper's fixed weak machine ("Pad it to the exact native width q(N) = ⌈log₂ T_clk(N)⌉ + A_pad ⌈log₂(log₂ T_clk(N) + 2)⌉ + A_pad …
so that ℓ_out ≤ q(N)"):
`q(N) = ⌈log₂ T_clk(N)⌉ + A_pad ⌈log₂(log₂ T_clk(N) + 2)⌉ + A_pad` with `T_clk(N) = N^{k+2}` (here `⌈log₂ T_clk⌉` is read
as `Nat.clog 2 (N^{k+2})`, and `log₂ T_clk` inside as the same integer). `envelope_le` is the arithmetic behind `ℓ_out ≤ q(N)`:
for `A_pad = padConst K c e`, every envelope `K · (c·N^{k+2}) · L(c·N^{k+2})^e` of the import's `2^ℓ` fits in `2^q`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Outer

open NearCubicWires

/-- `⌈log₂ T_clk(N)⌉`, `T_clk(N) = N^{k+2}`. -/
def clkLog (k N : ℕ) : ℕ := Nat.clog 2 (N ^ (k + 2))

/-- `q(N) = ⌈log₂ T_clk(N)⌉ + A ⌈log₂(⌈log₂ T_clk(N)⌉ + 2)⌉ + A`. -/
def widthOf (k A N : ℕ) : ℕ := clkLog k N + A * Nat.clog 2 (clkLog k N + 2) + A

/-- `A_pad` for the envelope constants `K`, `c`, `e` (chosen after them: paper App. C, the constant order, item 6, "An integer A_pad ≥ c_ℓ …"). -/
def padConst (K c e : ℕ) : ℕ := e + K * c * Nat.clog 2 (c + 2) ^ e

theorem clog_two_mul_pow_le (a l : ℕ) : Nat.clog 2 (a * 2 ^ l) ≤ Nat.clog 2 a + l := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) a)

/-- The arithmetic behind `ℓ_out ≤ q(N)`. -/
theorem envelope_le (K c e k N : ℕ) (hN : 1 ≤ N) :
    K * (c * N ^ (k + 2)) * logScale (c * N ^ (k + 2)) ^ e ≤ 2 ^ widthOf k (padConst K c e) N := by
  set lam := clkLog k N with hlam
  set mu := Nat.clog 2 (lam + 2) with hmu
  set κ := Nat.clog 2 (c + 2) with hκ
  set A := padConst K c e with hA
  have hNpow : 1 ≤ N ^ (k + 2) := Nat.one_le_pow _ _ hN
  have hT : N ^ (k + 2) ≤ 2 ^ lam := Nat.le_pow_clog (by norm_num) _
  have hκ1 : 1 ≤ κ := by
    rw [hκ]
    exact Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) (by omega))
  have hmu2 : lam + 2 ≤ 2 ^ mu := Nat.le_pow_clog (by norm_num) _
  -- the logarithmic factor
  have hL : logScale (c * N ^ (k + 2)) ≤ κ * (lam + 2) := by
    unfold logScale
    have h1 : c * N ^ (k + 2) + 2 ≤ (c + 2) * 2 ^ lam := by
      calc c * N ^ (k + 2) + 2 ≤ (c + 2) * N ^ (k + 2) := by nlinarith
        _ ≤ (c + 2) * 2 ^ lam := Nat.mul_le_mul_left _ hT
    calc Nat.clog 2 (c * N ^ (k + 2) + 2) ≤ Nat.clog 2 ((c + 2) * 2 ^ lam) := Nat.clog_mono_right _ h1
      _ ≤ κ + lam := clog_two_mul_pow_le _ _
      _ ≤ κ * (lam + 2) := by nlinarith
  have hLe : logScale (c * N ^ (k + 2)) ^ e ≤ κ ^ e * 2 ^ (mu * e) := by
    calc logScale (c * N ^ (k + 2)) ^ e ≤ (κ * (lam + 2)) ^ e := Nat.pow_le_pow_left hL _
      _ = κ ^ e * (lam + 2) ^ e := by rw [mul_pow]
      _ ≤ κ ^ e * (2 ^ mu) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmu2 _)
      _ = κ ^ e * 2 ^ (mu * e) := by rw [← pow_mul]
  have hAe : e ≤ A := by rw [hA, padConst]; omega
  have hAK : K * c * κ ^ e ≤ 2 ^ A := by
    have : K * c * κ ^ e ≤ A := by rw [hA, padConst, ← hκ]; omega
    exact this.trans (Nat.lt_two_pow_self).le
  have hmuA : 2 ^ (mu * e) ≤ 2 ^ (A * mu) :=
    Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_comm A]; exact Nat.mul_le_mul_left _ hAe)
  calc K * (c * N ^ (k + 2)) * logScale (c * N ^ (k + 2)) ^ e
      ≤ K * (c * 2 ^ lam) * (κ ^ e * 2 ^ (mu * e)) := by
        gcongr
    _ = (K * c * κ ^ e) * 2 ^ lam * 2 ^ (mu * e) := by ring
    _ ≤ 2 ^ A * 2 ^ lam * 2 ^ (A * mu) := by gcongr
    _ = 2 ^ widthOf k A N := by
        rw [widthOf, ← hlam, ← hmu, pow_add, pow_add]
        ring

/-- `ν + 1 ≤ q(2^ν)`: the source index fits in the width (CHECK reads `ν` of the `q` bits). -/
theorem succ_le_widthOf (k A ν : ℕ) (hA : 1 ≤ A) : ν + 1 ≤ widthOf k A (2 ^ ν) := by
  have hlam : ν ≤ clkLog k (2 ^ ν) := by
    unfold clkLog
    rw [← pow_mul, Nat.clog_pow 2 _ (by norm_num)]
    nlinarith
  unfold widthOf
  nlinarith

theorem clkLog_two_pow (k ν : ℕ) : clkLog k (2 ^ ν) = ν * (k + 2) := by
  unfold clkLog
  rw [← pow_mul, Nat.clog_pow 2 _ (by norm_num)]

/-- Once `2^T ≤ N`, `q(N) ≥ T` (the native width dominates every fixed threshold eventually). -/
theorem le_widthOf (k A T N : ℕ) (hN : 2 ^ T ≤ N) : T ≤ widthOf k A N := by
  have h1 : T ≤ clkLog k N := by
    unfold clkLog
    refine le_trans ?_ (Nat.log_le_clog 2 _)
    apply Nat.le_log_of_pow_le (by norm_num)
    calc 2 ^ T ≤ N := hN
      _ ≤ N ^ (k + 2) := Nat.le_self_pow (by omega) N
  unfold widthOf
  omega

theorem two_pow_clog_le (x : ℕ) : 2 ^ Nat.clog 2 x ≤ 2 * x + 1 := by
  rcases Nat.lt_or_ge x 2 with hx | hx
  · interval_cases x <;> simp [Nat.clog]
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < x)
    rw [Nat.pred_eq_sub_one] at h
    have hc : 1 ≤ Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
    have : 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- **`2^{q(N)}` is polynomial in `N`** (the near-cubic-gates paper's fixed weak machine: `2^q/T_clk(N) = q^{O(1)}`). -/
theorem widthOf_pow (k A : ℕ) : ∃ C m : ℕ, ∀ N, 2 ^ widthOf k A N ≤ C * (N + 1) ^ m := by
  refine ⟨2 ^ A * 3 * 11 ^ A, (k + 2) * (A + 1), fun N => ?_⟩
  set T := (N + 1) ^ (k + 2) with hT
  have hT1 : 1 ≤ T := Nat.one_le_pow _ _ (by omega)
  have hc : clkLog k N ≤ Nat.clog 2 T := Nat.clog_mono_right _ (Nat.pow_le_pow_left (by omega) _)
  have h1 : 2 ^ clkLog k N ≤ 3 * T := by
    have := two_pow_clog_le T
    exact (Nat.pow_le_pow_right (by norm_num) hc).trans (by omega)
  have h2 : 2 ^ Nat.clog 2 (clkLog k N + 2) ≤ 11 * T := by
    have hcl : clkLog k N + 2 ≤ 3 * T + 2 := by
      have h0 : clkLog k N < 2 ^ clkLog k N := Nat.lt_two_pow_self
      exact Nat.add_le_add_right (h0.le.trans h1) 2
    calc 2 ^ Nat.clog 2 (clkLog k N + 2) ≤ 2 ^ Nat.clog 2 (3 * T + 2) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.clog_mono_right _ hcl)
      _ ≤ 2 * (3 * T + 2) + 1 := two_pow_clog_le _
      _ ≤ 11 * T := by omega
  unfold widthOf
  rw [pow_add, pow_add, pow_mul', Nat.mul_comm]
  calc 2 ^ A * (2 ^ clkLog k N * (2 ^ Nat.clog 2 (clkLog k N + 2)) ^ A)
      ≤ 2 ^ A * (3 * T * (11 * T) ^ A) := by gcongr
    _ = 2 ^ A * 3 * 11 ^ A * T ^ (A + 1) := by rw [mul_pow, pow_succ]; ring
    _ = 2 ^ A * 3 * 11 ^ A * (N + 1) ^ ((k + 2) * (A + 1)) := by rw [hT, ← pow_mul]

end NearCubicGates.Close.Outer
