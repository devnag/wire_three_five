import Proof.Wire_3_5.Primitive.Writers.SBRunBase

/-! # SB, part (6): S4's words `4 … 7` as a writer (`S4WordsMBJ l`)

* `clearAllCost_eq`, `A0`, `CsOf`, `DsOf`, **`sb_contract`** (the writer's run at the capacity `Kc F·(N+1)^{Dk fe}`,
  from the arithmetic targets with explicit constants);
* **`sbWriter`**: `Finish.S4WordsMBJ l` from `SBIdentStmts l`, `SBOutsStmt l` (the identifications and `sb_outs`),
  `SBCostStmt l`, `SBFieldCostStmt l`, `SBCapStmt l` (the arithmetic targets).

Paper quantity of the main type: S4's words `4 … 7` at a star call (`s4Core2`: the field words, the walk's threshold,
`s4Small2`; P3:3170-3181) within `prim:runtime` (P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Out.Car NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums NearCubicWires.WireExponent3_5.PrimAsm.SBTypes

theorem clearAllCost_eq (cap : ℕ) : ∀ k : ℕ, SBInv.clearAllCost cap k = k * (3 * cap + 2)
  | 0 => by simp [SBInv.clearAllCost]
  | k + 1 => by
    show 3 * cap + 1 + 1 + SBInv.clearAllCost cap k = (k + 1) * (3 * cap + 2)
    rw [clearAllCost_eq cap k]; ring

/-- The carrier pipeline's coefficient. -/
noncomputable def A0 : ℕ := 57600 * (DtC + 1) + 10 ^ 6

/-- The writer's step coefficient from the capacity coefficient. -/
noncomputable def CsOf (Cc E Cf Ef k : ℕ) : ℕ := (A0 + Cc + Cf + 1000) * (k + 1) ^ (E + Ef + 2)

/-- The writer's step degree from the capacity degree. -/
def DsOf (E Ef d : ℕ) : ℕ := (E + Ef + 2) * d

theorem cap_pow (Cc E Cf Ef k N d K : ℕ) (hK : K = k * (N + 1) ^ d) (h1 : 1 ≤ K) :
    K ^ (E + Ef + 2) ≤ CsOf Cc E Cf Ef k * (N + 1) ^ DsOf E Ef d ∧ (A0 + Cc + Cf + 1000) * K ^ (E + Ef + 2) ≤
      CsOf Cc E Cf Ef k * (N + 1) ^ DsOf E Ef d := by
  have e1 : K ^ (E + Ef + 2) ≤ (k + 1) ^ (E + Ef + 2) * (N + 1) ^ DsOf E Ef d := by
    rw [hK, mul_pow, DsOf, mul_comm (E + Ef + 2) d, pow_mul]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
  have e2 : (A0 + Cc + Cf + 1000) * K ^ (E + Ef + 2) ≤ CsOf Cc E Cf Ef k * (N + 1) ^ DsOf E Ef d := by
    unfold CsOf; rw [mul_assoc]; exact Nat.mul_le_mul_left _ e1
  refine ⟨le_trans ?_ e2, e2⟩
  exact Nat.le_mul_of_pos_left _ (by omega)

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
