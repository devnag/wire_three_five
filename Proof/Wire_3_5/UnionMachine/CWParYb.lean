import Proof.Wire_3_5.UnionMachine.CWParFit

/-! # C6 front, U5, the code writers: polynomial bounds in powers of `Y ≥ 9`

A toolkit for the parity writer's time bound (P3:3092-3094; the interface's `K·(n+1)^d`): with `Y ≥ 9`, every
constant, sum and product of quantities bounded by powers of `Y` is bounded by a power of `Y`.

Paper quantity: none (arithmetic). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParYb

variable {Y : ℕ}

theorem ypos (hY : 9 ≤ Y) (e : ℕ) : 1 ≤ Y ^ e := Nat.one_le_pow _ _ (by omega)

theorem yle (hY : 9 ≤ Y) {x a b : ℕ} (hab : a ≤ b) (hx : x ≤ Y ^ a) : x ≤ Y ^ b :=
  hx.trans (Nat.pow_le_pow_right (by omega) hab)

theorem yc (hY : 9 ≤ Y) (c e : ℕ) (hc : c ≤ 9 ^ e) : c ≤ Y ^ e := hc.trans (Nat.pow_le_pow_left hY e)

theorem ym {x y a b : ℕ} (hx : x ≤ Y ^ a) (hy : y ≤ Y ^ b) : x * y ≤ Y ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem ypw {x a : ℕ} (k : ℕ) (hx : x ≤ Y ^ a) : x ^ k ≤ Y ^ (a * k) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx k

/-- `c·x + d` with `c + d ≤ 9^k`. -/
theorem ylin (hY : 9 ≤ Y) {x e : ℕ} (hx : x ≤ Y ^ e) (c d k : ℕ) (hc : c + d ≤ 9 ^ k) :
    c * x + d ≤ Y ^ (e + k) := by
  have h1 := ypos hY e
  have h2 : c * x + d ≤ (c + d) * Y ^ e := by nlinarith
  have h3 : (c + d) * Y ^ e ≤ Y ^ k * Y ^ e := Nat.mul_le_mul_right _ (yc hY _ _ hc)
  rw [pow_add]; nlinarith

/-- A sum of two. -/
theorem yadd (hY : 9 ≤ Y) {x y e : ℕ} (hx : x ≤ Y ^ e) (hy : y ≤ Y ^ e) : x + y ≤ Y ^ (e + 1) := by
  rw [pow_succ]; nlinarith

end NearCubicWires.WireExponent3_5.UnionMachine.CWParYb
