import Proof.Wire_3_5.Primitive.SeedFix.C4CapF
import Proof.Wire_3_5.Primitive.SeedFix.C4CapE

/-! # C4.K item (h), part 1: a calculus of rates `2^{j·⌊n/8⌋ + c}` against the table class `2^{n−k}` (generic)

P3:3098-3100, 3105-3115 (the seed-fixing budget `c₄·seedClasses E₄ q k ψ`, with the table term `2^{q−k}·q^{A_table}`):
the envelope `E₄` is fixed before the gate `F`, only `c₄` after it. So the stage's cost is split into terms of rate at
most `7/8` (`Ex n j c X`: `X ≤ 2^{j·⌊n/8⌋ + c}`, `j ≤ 7`, every constant `c` free to depend on `F`), which fall below
`2^{c + K₀}·2^{n−k}` since `k ≤ n/16 + K₀`, and the table-rate terms `2^{n−k}·poly(n)` of an `F`-free degree.

* `Ex`, `ex_le`, `ex_mono`, `ex_add`, `ex_mul`, `ex_const`, `ex_pow2`, `ex_poly`, `ex_s`, **`ex_final`**.

Paper quantity of the main type: the stage's steps against the table class `2^{q−k}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.WireExponent3_5

/-- **A term of rate `j/8`**: `X ≤ 2^{j·⌊n/8⌋ + c}`. -/
def Ex (n j c X : ℕ) : Prop := X ≤ 2 ^ (j * (n / 8) + c)

theorem ex_le {n j c X Y : ℕ} (h : X ≤ Y) (hY : Ex n j c Y) : Ex n j c X := le_trans h hY

theorem ex_mono {n j c j' c' X : ℕ} (hj : j ≤ j') (hc : c ≤ c') (h : Ex n j c X) : Ex n j' c' X :=
  le_trans h (Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add (Nat.mul_le_mul_right _ hj) hc))

theorem ex_add {n j a b X Y : ℕ} (hX : Ex n j a X) (hY : Ex n j b Y) : Ex n j (a + b + 1) (X + Y) := by
  unfold Ex at *
  have h1 : X ≤ 2 ^ (j * (n / 8) + (a + b)) := le_trans hX (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : Y ≤ 2 ^ (j * (n / 8) + (a + b)) := le_trans hY (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 : 2 ^ (j * (n / 8) + (a + b + 1)) = 2 ^ (j * (n / 8) + (a + b)) * 2 := by rw [← pow_succ]; ring_nf
  omega

theorem ex_s (e : ℕ) : ∃ c : ℕ, ∀ n : ℕ, Ex n 1 c (2 ^ (e * (natBitLength n + 1) ^ 2)) := by
  obtain ⟨K0, hK0⟩ := C4Cap.mul_sq_le_div16 e
  refine ⟨K0, fun n => ?_⟩
  unfold Ex
  exact Nat.pow_le_pow_right (by norm_num) (by have := hK0 n; omega)

theorem ex_poly (D : ℕ) : ∃ c : ℕ, ∀ n : ℕ, Ex n 1 c ((n + 1) ^ D) := by
  obtain ⟨c, hc⟩ := ex_s D
  refine ⟨c, fun n => ex_le ?_ (hc n)⟩
  have h1 : n + 1 ≤ 2 ^ (natBitLength n + 1) := le_trans (Nat.le_succ _) (C4Cap.n2_le n)
  have h2 : natBitLength n + 1 ≤ (natBitLength n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  calc (n + 1) ^ D ≤ (2 ^ (natBitLength n + 1)) ^ D := Nat.pow_le_pow_left h1 D
    _ = 2 ^ (D * (natBitLength n + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (D * (natBitLength n + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h2)

/-- **Rate `7/8` is below the table rate**: with `k ≤ n/16 + K₀`, `2^{7⌊n/8⌋ + c} ≤ 2^{c + K₀}·2^{n−k}`. -/
theorem ex_final {n c k K0 X : ℕ} (h : Ex n 7 c X) (hk : k ≤ n / 16 + K0) : X ≤ 2 ^ (c + K0) * 2 ^ (n - k) := by
  unfold Ex at h
  rw [← pow_add]
  exact le_trans h (Nat.pow_le_pow_right (by norm_num) (by omega))

end NearCubicWires.WireExponent3_5.PrimT.C4Bud
