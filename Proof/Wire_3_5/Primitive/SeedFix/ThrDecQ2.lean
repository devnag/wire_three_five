import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ1

/-! # THR decode front, packaging part 2: the front's capacity needs below `c₀ = Q^i·2^{K·L²}`

At a THR call every quantity the front writes into a register (the request's length, the THR numbers, the carriers'
sizes, the THR filter's parameters and seed length, `2^{2k_h} = N²`, the docks' count) is at most `Q·2^{A·L²}` with
`A` fixed before the gate and `Q` after it. **`fneed_arith`**: from those atom bounds, the front's capacity needs
`FNeed` at the virtual capacity `c₀ = Q^{A+9}·2^{(A² + 60A + 60)·L²}`.

* `QY` (`Q^i·2^{a·Y}`), `qy_mono`, `qy_mul`, `qy_add`, `qy_const`, `qy_pow`; **`fneed_arith`**.

Paper quantity of the main type: the front's capacity within the expansion class `2^{O(L²)}` (P3:2597-2599). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters

/-- `Q^i·2^{a·Y}`. -/
def QY (Q Y i a : ℕ) : ℕ := Q ^ i * 2 ^ (a * Y)

theorem qy_mono {Q Y i a i' a' X : ℕ} (hQ : 1 ≤ Q) (h : X ≤ QY Q Y i a) (hi : i ≤ i') (ha : a ≤ a') :
    X ≤ QY Q Y i' a' := by
  unfold QY at *
  exact h.trans (Nat.mul_le_mul (Nat.pow_le_pow_right hQ hi)
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ha)))

theorem qy_mul {Q Y i a j b X Z : ℕ} (hX : X ≤ QY Q Y i a) (hZ : Z ≤ QY Q Y j b) :
    X * Z ≤ QY Q Y (i + j) (a + b) := by
  unfold QY at *
  calc X * Z ≤ (Q ^ i * 2 ^ (a * Y)) * (Q ^ j * 2 ^ (b * Y)) := Nat.mul_le_mul hX hZ
    _ = Q ^ (i + j) * 2 ^ ((a + b) * Y) := by rw [pow_add, add_mul, pow_add]; ring

theorem qy_add {Q Y i a X Z : ℕ} (hY : 1 ≤ Y) (hX : X ≤ QY Q Y i a) (hZ : Z ≤ QY Q Y i a) :
    X + Z ≤ QY Q Y i (a + 1) := by
  unfold QY at *
  have h2 : 2 * 2 ^ (a * Y) ≤ 2 ^ ((a + 1) * Y) := by
    rw [add_mul, one_mul, pow_add]
    have : 2 ≤ 2 ^ Y := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Y := Nat.pow_le_pow_right (by norm_num) hY
    nlinarith [Nat.one_le_two_pow (n := a * Y)]
  calc X + Z ≤ Q ^ i * 2 ^ (a * Y) + Q ^ i * 2 ^ (a * Y) := Nat.add_le_add hX hZ
    _ = Q ^ i * (2 * 2 ^ (a * Y)) := by ring
    _ ≤ Q ^ i * 2 ^ ((a + 1) * Y) := Nat.mul_le_mul_left _ h2

theorem qy_pow {Q Y i a X : ℕ} (hX : X ≤ QY Q Y i a) (e : ℕ) : X ^ e ≤ QY Q Y (i * e) (a * e) := by
  induction e with
  | zero => unfold QY; simp
  | succ e ih =>
    rw [pow_succ]
    have h := qy_mul ih hX
    have e1 : i * e + i = i * (e + 1) := by ring
    have e2 : a * e + a = a * (e + 1) := by ring
    rw [e1, e2] at h
    exact h

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
