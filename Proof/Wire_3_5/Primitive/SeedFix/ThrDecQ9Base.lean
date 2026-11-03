import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ8Base

/-! # T3 THR decode front, packaging part 9: `ThrDecFront` and its uniform family

**`thrDecFront x hx : ThrDec.ThrDecFront x l F`** at every cell layout `x ≥ dX (TW l) (NW l)`: the machine `frontM`, the
capacity `need n = c₀(n) = cZero (Q_F) (L²) (aE l f_e)` and the cost `bound n = fK·(c₀(n)+1)^{fD}`, both
quasi-bounded with exponents `nK l f_e`, `bK l f_e` from `(l, f_e)` only and coefficients from `F`; the run at every
THR call, unit and capacity `≥ need n + j` (`call_run`). **`thrDecU`**: the fronts as a uniform family
(`Seams.StageU`, `ThrUnit.decDeg`/`decCf`) at any cells `xF F ≥ dX (TW l) (NW l)`.

Paper quantity of the main type: the THR call's rows (FILTER and RADIX) at each unit of the THR tape within
`2^{O(L²)}` (P3:2543-2558, 2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine



theorem qb_of_QY {Q X n i a : ℕ} (h : X ≤ QY Q (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)) i a) :
    PrimThrW.RadSetup.QuasiBounded X n (Q ^ i) 0 a := by
  unfold PrimThrW.RadSetup.QuasiBounded
  unfold QY at h
  rw [pow_zero, mul_one, pow_two]
  exact h

theorem UQ_two (Q Y A : ℕ) (hQ : 1 ≤ Q) (hY : 1 ≤ Y) : 2 ≤ UQ Q Y A := by
  unfold UQ QY
  have h1 : 2 ^ 1 ≤ 2 ^ ((A + 2) * Y) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : 1 ≤ Q ^ 1 := by simpa using hQ
  calc 2 = 1 * 2 ^ 1 := by norm_num
    _ ≤ Q ^ 1 * 2 ^ ((A + 2) * Y) := Nat.mul_le_mul h2 h1

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
