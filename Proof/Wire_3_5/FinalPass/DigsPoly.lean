import Proof.Wire_3_5.FinalPass.DigsTop1

/-! # `DigsW`'s body, part 19: the program's bound is polynomial (`DigsW.bound_le`)

`PolyB f`: `f U ≤ C · (U + 1)^D` for all `U`. Closed under constants, the identity, sums and products, so every
uniform bound of the program (`topB`, built from `+` and `·`) is `PolyB` (`topB_poly`); substituting a polynomial
size (`U = 16 (N + 1)^4`) keeps it polynomial (`PolyB.subst`). Main declarations: `PolyB`, `PolyB.add`, `PolyB.mul`,
**`topB_poly`**, `PolyB.subst`. Paper quantity: none (the digit program's running time, polynomial in the input). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.ThrCore NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires.WireExponent3_5.FinalPass.ThrArith

/-- A polynomial bound. -/
def PolyB (f : ℕ → ℕ) : Prop := ∃ C D : ℕ, ∀ U, f U ≤ C * (U + 1) ^ D

theorem PolyB.const (c : ℕ) : PolyB fun _ => c := ⟨c, 0, fun U => by simp⟩

theorem PolyB.id : PolyB fun U => U := ⟨1, 1, fun U => by simp⟩

theorem PolyB.add {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun U => f U + g U := by
  obtain ⟨C1, D1, h1⟩ := hf
  obtain ⟨C2, D2, h2⟩ := hg
  refine ⟨C1 + C2, D1 + D2, fun U => ?_⟩
  have e1 : (U + 1) ^ D1 ≤ (U + 1) ^ (D1 + D2) := Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (U + 1) ^ D2 ≤ (U + 1) ^ (D1 + D2) := Nat.pow_le_pow_right (by omega) (by omega)
  have := h1 U
  have := h2 U
  have := Nat.mul_le_mul_left C1 e1
  have := Nat.mul_le_mul_left C2 e2
  nlinarith

theorem PolyB.mul {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB fun U => f U * g U := by
  obtain ⟨C1, D1, h1⟩ := hf
  obtain ⟨C2, D2, h2⟩ := hg
  refine ⟨C1 * C2, D1 + D2, fun U => ?_⟩
  calc f U * g U ≤ (C1 * (U + 1) ^ D1) * (C2 * (U + 1) ^ D2) := Nat.mul_le_mul (h1 U) (h2 U)
    _ = C1 * C2 * (U + 1) ^ (D1 + D2) := by rw [pow_add]; ring

/-- The program's bound is polynomial. -/
theorem topB_poly : PolyB topB := by
  unfold topB dB bB cDB cBB navB wCost modCost2 coreCost bitCost2 bitCost ThrArith.mulStep bitOfCost halfCost encCost
    bUpdCost
  repeat (first | apply PolyB.add | apply PolyB.mul | exact PolyB.id | exact PolyB.const _)

/-- Substituting a polynomial size. -/
theorem PolyB.subst {f : ℕ → ℕ} (hf : PolyB f) (a k : ℕ) :
    ∃ C D : ℕ, ∀ N, f (a * (N + 1) ^ k) ≤ C * (N + 1) ^ D := by
  obtain ⟨C, D, h⟩ := hf
  refine ⟨C * (a + 1) ^ D, k * D, fun N => ?_⟩
  have e : a * (N + 1) ^ k + 1 ≤ (a + 1) * (N + 1) ^ k := by
    have : 1 ≤ (N + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc f (a * (N + 1) ^ k) ≤ C * (a * (N + 1) ^ k + 1) ^ D := h _
    _ ≤ C * ((a + 1) * (N + 1) ^ k) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e D)
    _ = C * (a + 1) ^ D * (N + 1) ^ (k * D) := by rw [mul_pow, ← pow_mul]; ring

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
