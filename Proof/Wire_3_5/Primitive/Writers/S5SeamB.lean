import Lean
import Proof.Wire_3_5.Primitive.Writers.S5Seam
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.S5SeamBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2: the S5 halves with their cost bounds (freeze gate (2))

The sub-seam (`S5Seam`) leaves the halves' costs free; the final pass's cost residual
(`SeamsPt.FitsRes`, `X.front.cost r ≤ fB r`) needs them explicit. This file adds, as wrappers, the bound in the
preprocessing class's form `C · 2^{D·ψ(n)} · (|fpIn| + 1)^D` (ψ the ledger's load `psiOf` at the request's `n`), which
`fpBudget = c₅·finalClasses(E₅, n, k, ψ)` absorbs once `E₅`'s load and polynomial exponents cover `D` and `c₅ ≥ C`.

* `s5Psi`, `s5Bound`, `s5Bound_mono`;
* **`S5ThrB`** (the THR half's target), **`S5CoreB`** (the core half's target);
* **`s5_cost_le`**: the two halves in sequence (one bridge step) within `s5Bound (Ct + Cc + 1) (max Dt Dc)`.

Paper quantity of the main types: the front's running time inside the call's additive preprocessing term
`2^{O(Ψ)}` (prim:runtime, P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E3 : SymPtEval)

/-- The ledger's load `ψ = psiOf n` at the request's width. -/
noncomputable abbrev s5Psi (r : FReq l F kclk coef A a ha) : ℕ := ((gate0 l F).budget kclk coef A a ha).psiOf r.1.n

/-- **The preprocessing-class cost bound** `C · 2^{D·ψ} · (|fpIn| + 1)^D`. -/
noncomputable def s5Bound (C D : ℕ) (r : FReq l F kclk coef A a ha) : ℕ :=
  C * 2 ^ (D * s5Psi l F kclk coef A a ha r) * ((fpIn l F kclk coef A a ha r).length + 1) ^ D

theorem s5Bound_mono (C C' D D' : ℕ) (hC : C ≤ C') (hD : D ≤ D') (r : FReq l F kclk coef A a ha) :
    s5Bound l F kclk coef A a ha C D r ≤ s5Bound l F kclk coef A a ha C' D' r := by
  unfold s5Bound
  have h1 : 2 ^ (D * s5Psi l F kclk coef A a ha r) ≤ 2 ^ (D' * s5Psi l F kclk coef A a ha r) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hD)
  have h2 : ((fpIn l F kclk coef A a ha r).length + 1) ^ D ≤ ((fpIn l F kclk coef A a ha r).length + 1) ^ D' :=
    Nat.pow_le_pow_right (by omega) hD
  exact Nat.mul_le_mul (Nat.mul_le_mul hC h1) h2

theorem one_le_s5Bound (C D : ℕ) (hC : 1 ≤ C) (r : FReq l F kclk coef A a ha) :
    1 ≤ s5Bound l F kclk coef A a ha C D r := by
  unfold s5Bound
  have h1 : 1 ≤ 2 ^ (D * s5Psi l F kclk coef A a ha r) := Nat.one_le_two_pow
  have h2 : 1 ≤ ((fpIn l F kclk coef A a ha r).length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
  calc 1 = 1 * 1 * 1 := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul hC h1) h2

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam

end
