import Proof.Wire_3_5.Primitive.SeedFix.W6ZD

/-! # W6, part 31: the fixed hash's numbers are polynomial in the call's base

P3:2121-2157 and P3:2220-2231 (filt:majorant, filt:soft: `J = ⌈log₂(8KAB_*+1)⌉`, `t = ⌈log₂(8KAJ+1)⌉+1`,
`e = ⌈log₂(8KA(M + J M^{2t}) + 1)⌉ + 1`, `ℓ₀ = max (J+1) ⌈log₂ M⌉`, the modulus `< 2^{ℓ₀+1}`, the EW stage's need): each
at most a power of the call's base `N`:
* `bKAB`, `bClog`, `b2Clog`, **`listE_le`** (`e ≤ 8KA + J + 2tM + M + 3`, from `x < 2^x`), `bL0`, `b2L0`, `bMod`, `bEw`.

Paper quantities of the main types: `J`, `t`, `e`, `ℓ₀`, the modulus, each `≤ N^{O(D)}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires

theorem mul_succ_le_two_pow {X Y a b : ℕ} (hX : X ≤ 2 ^ a) (hY : Y ≤ 2 ^ b) : X * Y + 1 ≤ 2 ^ (a + b + 1) := by
  have h := Nat.mul_le_mul hX hY
  rw [← pow_add] at h
  have h1 : 1 ≤ 2 ^ (a + b) := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem pow_two_mul_le (M t : ℕ) : M ^ (2 * t) ≤ 2 ^ (M * (2 * t)) := by
  calc M ^ (2 * t) ≤ (2 ^ M) ^ (2 * t) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ (M * (2 * t)) := by rw [← pow_mul]

theorem sum_le_two_pow (M J t : ℕ) : M + J * M ^ (2 * t) ≤ 2 ^ (J + M * (2 * t) + M + 1) := by
  have hJ : J < 2 ^ J := Nat.lt_two_pow_self
  have hM : M < 2 ^ M := Nat.lt_two_pow_self
  have hJM : J * M ^ (2 * t) ≤ 2 ^ (J + M * (2 * t)) := by
    rw [pow_add]; exact Nat.mul_le_mul hJ.le (pow_two_mul_le M t)
  have a1 : 2 ^ M ≤ 2 ^ (J + M * (2 * t) + M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have a2 : 2 ^ (J + M * (2 * t)) ≤ 2 ^ (J + M * (2 * t) + M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e := pow_succ 2 (J + M * (2 * t) + M)
  omega

/-- **The aux filter's `e`**, by `x < 2^x`: `e ≤ 8KA + J + 2tM + M + 3`. -/
theorem listE_le (A B M K : ℕ) : Primitive.listE A B M K ≤
    8 * K * A + Primitive.listJ A B K + 2 * Primitive.listT A B K * M + M + 3 := by
  unfold Primitive.listE
  generalize Primitive.listJ A B K = J
  generalize Primitive.listT A B K = t
  have hP := mul_succ_le_two_pow (Nat.lt_two_pow_self (n := 8 * K * A)).le (sum_le_two_pow M J t)
  have hc := Nat.clog_le_of_le_pow hP
  have e : M * (2 * t) = 2 * t * M := by ring
  rw [e] at hc
  omega

theorem bClog {N : ℕ} (x e : ℕ) (hx : x + 1 ≤ N ^ e) : Nat.clog 2 (x + 1) ≤ N ^ e :=
  (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans hx

theorem bMod {N : ℕ} (ℓ e : ℕ) (h : 2 ^ (ℓ + 1) ≤ N ^ e) : GF.firstPrimitive ℓ ≤ N ^ e := by
  have hs := fp_split ℓ
  have hlt : GF.firstPrimitive ℓ % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt _ Nat.one_le_two_pow
  have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  omega

variable {N : ℕ} (hN : 16 ≤ N)
include hN

theorem bKAB (K A B eK eA eB : ℕ) (hK : K ≤ N ^ eK) (hA : A ≤ N ^ eA) (hB : B ≤ N ^ eB) :
    8 * K * A * B + 3 ≤ N ^ (eK + eA + eB + 2) := by
  have h8 : 8 ≤ N ^ 1 := by rw [pow_one]; omega
  have h := pw_mul (pw_mul (pw_mul h8 hK) hA) hB
  have h' := pw_succ hN h 3 (by omega)
  rw [show 1 + eK + eA + eB + 1 = eK + eA + eB + 2 by ring] at h'
  exact h'

theorem b2Clog (x e : ℕ) (hx : x + 1 ≤ N ^ e) : 2 ^ Nat.clog 2 (x + 1) ≤ N ^ (e + 1) := by
  have h := UnionMachine.EwKit.pow_clog_le2 (x + 1) (by omega)
  have h1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

theorem b2L0 (J M e : ℕ) (h2J : 2 ^ J ≤ N ^ e) (hM : M ≤ N ^ 2) (he : 2 ≤ e) :
    2 ^ (max (J + 1) (Nat.clog 2 M) + 1) ≤ N ^ (e + 2) := by
  have hcM : 2 ^ Nat.clog 2 M ≤ 2 * M + 1 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp
    · have := UnionMachine.EwKit.pow_clog_le2 M h; omega
  have hM' : M ≤ N ^ e := pw_mono (by omega) hM he
  have hmax : 2 ^ (max (J + 1) (Nat.clog 2 M) + 1) ≤ 2 ^ (J + 2) + 2 ^ (Nat.clog 2 M + 1) := by
    rcases le_total (J + 1) (Nat.clog 2 M) with h | h
    · rw [max_eq_right h]; exact Nat.le_add_left _ _
    · rw [max_eq_left h]; exact Nat.le_add_right _ _
  have h1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
  have e2 : N ^ (e + 2) = N ^ e * N * N := by rw [pow_succ, pow_succ]
  have p2 : 2 ^ (J + 2) = 4 * 2 ^ J := by rw [pow_add]; ring
  have p1 : 2 ^ (Nat.clog 2 M + 1) = 2 * 2 ^ Nat.clog 2 M := by rw [pow_succ]; ring
  rw [e2]
  have hNN : 16 * 16 ≤ N * N := Nat.mul_le_mul hN hN
  nlinarith

theorem bEw (M A B K e : ℕ) (hM : M ≤ N ^ e) (hA : A ≤ N ^ e) (hB : B ≤ N ^ e) (hK : K ≤ N ^ e) :
    UnionMachine.EwSize.ewNeed (M + A + B + K) ≤ N ^ (12 * (e + 1) + 11) := by
  unfold UnionMachine.EwSize.ewNeed
  have h1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
  have hs : M + A + B + K + 1 ≤ N ^ (e + 1) := by
    rw [pow_succ]; nlinarith
  have hp := Nat.pow_le_pow_left hs 12
  rw [← pow_mul] at hp
  have h11 : 10 ^ 13 ≤ N ^ 11 := by
    have : 16 ^ 11 ≤ N ^ 11 := Nat.pow_le_pow_left hN 11
    have e16 : (10 : ℕ) ^ 13 ≤ 16 ^ 11 := by norm_num
    omega
  rw [show 12 * (e + 1) + 11 = 11 + (e + 1) * 12 by ring, pow_add]
  exact Nat.mul_le_mul h11 hp

end NearCubicWires.WireExponent3_5.PrimT.W6
