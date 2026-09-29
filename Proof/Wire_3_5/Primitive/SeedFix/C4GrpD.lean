import Proof.Wire_3_5.Primitive.SeedFix.C4GrpC

/-! # C4.K side conditions, part 4: the counter's width below `qG` (for `cellCost_le`)

P3:3011-3016: the enumeration counter's width with the state word, `wT X = w + TWd = 8 + 8ℓ + 8kh + TWd`, is below
the group's size bound `qG` at the call: `qG ≥ 8ℓ + TWd + 8 + Fs` and `Fs ≥ T₀ + 2 ≥ 32kh`.

* **`wT_le_qG`**.

Paper quantity of the main type: the enumeration counter's width against the group's size bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Grp
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler

theorem Fs_ge (P : SeedParams) (R b : ℕ) (hb : 1 ≤ b) : T0 P + 2 ≤ Fs P R b := by
  have h1 : 1 ≤ b ^ (8 * R) := Nat.one_le_pow _ _ hb
  have h2 : T0 P + 8 * R * b + 1 ≤ b ^ (8 * R) * (T0 P + 8 * R * b + 1) := Nat.le_mul_of_pos_left _ h1
  unfold Fs; omega

/-- **The counter's width is below `qG`.** -/
theorem wT_le_qG (P : SeedParams) (ents : List (List SExpr)) (nT R TWd Cap : ℕ) (p' : List Bool) (b : ℕ)
    (hb : 1 ≤ b) : SplitT.wT (C4Enum.jX P ents TWd Cap p') ≤ qG P nT R b TWd p'.length := by
  have h1 := Fs_ge P R b hb
  have h2 := Nat.le_mul_of_pos_left (Fs P R b) (by omega : 0 < nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1)
  show 8 + 8 * P.ell + 8 * P.kh + TWd ≤ _
  unfold qG
  unfold T0 at h1
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Grp
