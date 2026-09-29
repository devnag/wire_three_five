import Proof.Wire_3_5.Primitive.Writers.TplLenB

/-! # TplLenC, part 3: the template length program's constants and cost, in a cleared context

The interface constants **`tplKt = 10³⁶`**, **`tplEt = 6`** (`TplIface Kt Et`), and the arithmetic of the run at
the inner capacity `c = capI M B L = 10⁹(M+B+L+2)²`, with every quantity abstract:

* `stepCost_le'`: one square-root step within `200(X+2)²`;
* **`cost_le`**: the three parts' costs (`p1_spec`, `p2_spec`, `p3_spec`) within `10⁸(c+2)³`;
* **`capI_cube`**: `10⁸(capI+2)³ ≤ 10³⁶(M+B+L+2)⁶`; `capI_le`: `capI ≤ 10³⁶(M+B+L+2)⁶`.

Paper quantity of the main type: the stage-5 template length's cost (prim:runtime P3:3105-3115, 3170-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.TplLenC
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm

/-- The template length interface's constant. -/
def tplKt : ℕ := 10 ^ 36

/-- The template length interface's exponent. -/
def tplEt : ℕ := 6

theorem stepCost_le' (X S : ℕ) (hS : S ≤ X + 1) : LevelW.stepCost X S ≤ 200 * ((X + 2) * (X + 2)) := by
  unfold LevelW.stepCost
  have h1 : S * S ≤ (X + 2) * (X + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : S * (18 * S + 8) = 18 * (S * S) + 8 * S := by ring
  have h3 : X + 2 ≤ (X + 2) * (X + 2) := Nat.le_mul_of_pos_left _ (by omega)
  rw [h2]
  omega

/-- **The three parts' costs within `10⁸(c+2)³`.** -/
theorem cost_le (c X S J M w n1 n2 n3 : ℕ) (hX : X ≤ c) (hS : S ≤ X + 1) (hJ : J + 1 ≤ c) (hM : M ≤ c)
    (hw : w ≤ c) (h1 : n1 ≤ 5 * UnaryPow.sq c + 4)
    (h2 : n2 ≤ (18 * X + 3 + 1 + (3 + 1 + ((X + 1) * (LevelW.stepCost X S + 4) + 1))) + 1 +
      (UnaryPow.sq c + 1 + (UnaryPow.sq c + 1 + (UnaryPow.sq c + 1 + UnaryPow.sq c))))
    (h3 : n3 ≤ FinalPass.SymParts.Tmpl.tplWBound c J M + 1 + (UnaryPow.sq c + 1 +
      (5 * w + 1 + 1 + (4 * UnaryPow.sq c + 3)))) :
    n1 + 1 + (n2 + 1 + n3) ≤ 10 ^ 8 * (c + 2) ^ 3 := by
  obtain ⟨Y2, hY2⟩ : ∃ x, x = (c + 2) * (c + 2) := ⟨_, rfl⟩
  obtain ⟨Y3, hY3⟩ : ∃ x, x = (c + 2) * Y2 := ⟨_, rfl⟩
  have e3 : (c + 2) ^ 3 = Y3 := by rw [hY3, hY2]; ring
  have hsq : UnaryPow.sq c = 200 * Y2 := by unfold UnaryPow.sq; rw [hY2]; ring
  have hY : c + 2 ≤ Y2 := by rw [hY2]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hY23 : Y2 ≤ Y3 := by rw [hY3]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hst : LevelW.stepCost X S ≤ 200 * Y2 := by
    have h := stepCost_le' X S hS
    have h' : (X + 2) * (X + 2) ≤ Y2 := by rw [hY2]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  have hA : (X + 1) * (LevelW.stepCost X S + 4) ≤ 204 * Y3 := by
    have h := Nat.mul_le_mul (show X + 1 ≤ c + 2 by omega) (show LevelW.stepCost X S + 4 ≤ 204 * Y2 by omega)
    have e : (c + 2) * (204 * Y2) = 204 * Y3 := by rw [hY3]; ring
    omega
  have hT : FinalPass.SymParts.Tmpl.tplWBound c J M ≤ 48 * c + 100 + 30000 * Y3 := by
    unfold FinalPass.SymParts.Tmpl.tplWBound FinalPass.SymParts.Tmpl.tplBodyBound LevelW.phBound
    have hp : 2000 * (c + 2) * (c + 2) = 2000 * Y2 := by rw [hY2]; ring
    rw [hp, hsq]
    have h := Nat.mul_le_mul (show J + 1 ≤ c + 2 by omega)
      (show 4 * (2000 * Y2 + 20 * (200 * Y2)) + 200 * (c + 10) + 4 ≤ 30000 * Y2 by omega)
    have e : (c + 2) * (30000 * Y2) = 30000 * Y3 := by rw [hY3]; ring
    omega
  rw [e3]
  rw [hsq] at h1 h2 h3
  omega

/-- **The inner capacity's cube within `10³⁶(M+B+L+2)⁶`.** -/
theorem capI_cube (M B L : ℕ) : 10 ^ 8 * (TplLen.capI M B L + 2) ^ 3 ≤ 10 ^ 36 * (M + B + L + 2) ^ 6 := by
  unfold TplLen.capI
  have hZ : 1 ≤ (M + B + L + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e6 : (M + B + L + 2) ^ 6 = ((M + B + L + 2) ^ 2) ^ 3 := by rw [← pow_mul]
  rw [e6]
  generalize (M + B + L + 2) ^ 2 = Z at hZ ⊢
  have h : 10 ^ 9 * Z + 2 ≤ (10 ^ 9 + 2) * Z := by omega
  calc 10 ^ 8 * (10 ^ 9 * Z + 2) ^ 3 ≤ 10 ^ 8 * ((10 ^ 9 + 2) * Z) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)
    _ = (10 ^ 8 * (10 ^ 9 + 2) ^ 3) * Z ^ 3 := by ring
    _ ≤ 10 ^ 36 * Z ^ 3 := Nat.mul_le_mul_right _ (by norm_num)

/-- The inner capacity within `10³⁶(M+B+L+2)⁶`. -/
theorem capI_le (M B L : ℕ) : TplLen.capI M B L ≤ 10 ^ 36 * (M + B + L + 2) ^ 6 := by
  have h := capI_cube M B L
  have h2 : TplLen.capI M B L + 2 ≤ (TplLen.capI M B L + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

end NearCubicWires.WireExponent3_5.PrimT.TplLenC
