import Proof.Wire_3_5.Primitive.SeedFix.C4CapD

/-! # C4 capacity (item (b)), part 5: sizes below `2^{a(B+1)²}` (generic in the mode)

P3:3105-3115 (every size the per-call setup holds is `2^{O(k)}·poly(n)` at an on-star call, with `k = r·⌊log₂(n/r+1)⌋`
and `r = 2(⌊log₂ L⌋ + c_r)`, P3:1189): each such number is below `2^{a·(B+1)²}`, `B` the bit length of `n`, for a
constant `a`, and then fits the unary capacity `2·2^{capExp C n} + 2` once `C ≥ a + 1`.

* the closure rules `pw_mul`, `pw_add`, `pw_mono`, `pw_const`, `pw_exp`, `pw_lin`, `clog_pw`, `pw_K`;
* the fit `pw_fit`, `pw_fit1`, `pw_fit2`; the base sizes `n2_pw`, `lq_le`, `pow_pw`, `rowBr_le`, `starWidth_le_bsq`.

Paper quantity of the main type: the capacity `2^{capExp C n}` against the call's sizes `2^{O(k)}·poly(n)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Cap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

/-- `(B+1)²`, `B` the bit length of `n`. -/
def bsq (n : ℕ) : ℕ := (natBitLength n + 1) ^ 2

theorem bsq_pos (n : ℕ) : 1 ≤ bsq n := Nat.one_le_pow _ _ (Nat.succ_pos _)

theorem b1_le_bsq (n : ℕ) : natBitLength n + 1 ≤ bsq n := Nat.le_self_pow (by norm_num) _

/-! ## Closure rules -/

theorem pw_mul {X Y a b s : ℕ} (hX : X ≤ 2 ^ (a * s)) (hY : Y ≤ 2 ^ (b * s)) : X * Y ≤ 2 ^ ((a + b) * s) := by
  rw [add_mul, pow_add]; exact Nat.mul_le_mul hX hY

theorem pw_mono {X a b s : ℕ} (hab : a ≤ b) (hX : X ≤ 2 ^ (a * s)) : X ≤ 2 ^ (b * s) :=
  le_trans hX (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hab))

theorem pw_add {X Y a b s : ℕ} (hs : 1 ≤ s) (hX : X ≤ 2 ^ (a * s)) (hY : Y ≤ 2 ^ (b * s)) :
    X + Y ≤ 2 ^ ((a + b + 1) * s) := by
  have h1 : X ≤ 2 ^ ((a + b) * s) := pw_mono (Nat.le_add_right a b) hX
  have h2 : Y ≤ 2 ^ ((a + b) * s) := pw_mono (Nat.le_add_left b a) hY
  have e : (a + b + 1) * s = (a + b) * s + s := by ring
  have h3 : 2 ^ ((a + b) * s) * 2 ≤ 2 ^ ((a + b + 1) * s) := by
    rw [← pow_succ, e]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem pw_const {X c s : ℕ} (hs : 1 ≤ s) (hX : X ≤ c) : X ≤ 2 ^ (c * s) :=
  le_trans hX (le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hs)))

theorem pw_exp {e a s : ℕ} (he : e ≤ a * s) : 2 ^ e ≤ 2 ^ (a * s) := Nat.pow_le_pow_right (by norm_num) he

theorem pw_lin {e a s : ℕ} (he : e ≤ a * s) : e ≤ 2 ^ (a * s) := le_trans (Nat.lt_two_pow_self).le (pw_exp he)

theorem clog_pw {X a s : ℕ} (hX : X ≤ 2 ^ (a * s)) : Nat.clog 2 X ≤ a * s := Nat.clog_le_of_le_pow hX

theorem pw_K {X K D s : ℕ} (hs : 1 ≤ s) (hX : X ≤ K * 2 ^ (D * s)) : X ≤ 2 ^ ((Nat.clog 2 K + D) * s) := by
  have hK : K ≤ 2 ^ (Nat.clog 2 K * s) :=
    le_trans (Nat.le_pow_clog (by norm_num) K) (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hs))
  rw [add_mul, pow_add]
  exact le_trans hX (Nat.mul_le_mul_right _ hK)

/-! ## The fit -/

/-! ## The base sizes -/

theorem n2_le (n : ℕ) : n + 2 ≤ 2 ^ (natBitLength n + 1) := by
  have h : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h1 : 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.one_le_two_pow
  unfold natBitLength
  rw [pow_succ (2 : ℕ) (Nat.log 2 n + 1)]
  omega

theorem n2_pw (n : ℕ) : n + 2 ≤ 2 ^ (1 * bsq n) :=
  le_trans (n2_le n) (Nat.pow_le_pow_right (by norm_num) (by rw [one_mul]; exact b1_le_bsq n))

theorem lq_le (n : ℕ) : Ledger.Lq n ≤ natBitLength n + 1 := by
  unfold Ledger.Lq; exact Nat.clog_le_of_le_pow (n2_le n)

theorem lq_le_bsq (n : ℕ) : Ledger.Lq n ≤ bsq n := le_trans (lq_le n) (b1_le_bsq n)

theorem pow_pw (d n : ℕ) : (n + 2) ^ d ≤ 2 ^ (d * bsq n) :=
  le_trans (Nat.pow_le_pow_left (n2_pw n) d) (le_of_eq (by rw [← pow_mul, one_mul, Nat.mul_comm]))

theorem rowBr_le (cr n : ℕ) : Ledger.rowBr cr n ≤ 2 * (natBitLength n + 1 + cr) := by
  unfold Ledger.rowBr
  have h1 : Nat.log 2 (Ledger.Lq n) ≤ Ledger.Lq n := Nat.log_le_self 2 _
  have h2 := lq_le n
  omega

/-- **The star width is `O((B+1)²)`**: `r·⌊log₂(n/r+1)⌋ ≤ (2c_r + 2)(B+1)²` at `r = rowBr c_r n`. -/
theorem starWidth_le_bsq (cr n : ℕ) : starWidth (Ledger.rowBr cr n) n ≤ (2 * cr + 2) * bsq n := by
  have h1 := Ledger.starWidth_le (Ledger.rowBr cr n) n
  have h2 := rowBr_le cr n
  have h3 := lq_le n
  obtain ⟨x, hx⟩ : ∃ x, x = natBitLength n + 1 := ⟨_, rfl⟩
  have hb : bsq n = x ^ 2 := by rw [hx]; rfl
  rw [← hx] at h2 h3
  rw [hb]
  have hx1 : 1 ≤ x := by rw [hx]; exact Nat.succ_pos _
  have e1 : Ledger.rowBr cr n * Ledger.Lq n ≤ 2 * (x + cr) * x := Nat.mul_le_mul h2 h3
  have e2 : cr * x ≤ cr * (x * x) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left x hx1)
  have e3 : 2 * (x + cr) * x = 2 * (x * x) + 2 * (cr * x) := by ring
  have e4 : (2 * cr + 2) * x ^ 2 = 2 * (x * x) + 2 * (cr * (x * x)) := by ring
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Cap
