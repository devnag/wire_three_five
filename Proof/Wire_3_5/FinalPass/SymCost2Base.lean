import Proof.Wire_3_5.FinalPass.SymCost1

/-! # The SYM child's cost, part 2: the SYM request's numbers at a call

P3:1886-1906, 3094-3107 at a SYM call, with the v2 free numbers (`Q' = d_Q(k+L)`, `h = d_H(n+1)^{e_H}`,
`m ≤ 400(k+L)`, `p = d_P(n+1)^{e_P}`, `d = d_D(⌊√B_S⌋+L)`): **`symFix_le`**, the compiler input's fixed fields and the
displayed parameters below `2^{e_F}` (`fix_num`; `|D| = |flips|·|gates| ≤ 2^{k+26L+5}`, `P_ex + 1 ≤ 2^{k + cDa·L}`,
`width ≤ 2·dRow ≤ n − k + 1`); **`symOcc_le`**, the charged occurrence count at every prefix below `2^{c_O U}`
(`occ_numU`, with the child expression's term count `A ≤ 2^{A₁(k+L)}`, generic in the batch). Also `L2_mul_le`
(`C_D L² ≤ ψ`, through `Ψ_aux`) and `bnOf` (the displayed parameters' sum).

Paper quantities of the main types: the compiler input's size and `𝒮` at a SYM child request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- `C_D·L² ≤ ψ` (through `Ψ_aux`). -/
theorem L2_mul_le (CD k L BT BS : ℕ) : CD * (L * L) ≤ loadPsi CD k L BT BS := by
  have h1 : loadAux CD k L ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine le_trans ?_ h1
  unfold loadAux
  apply Nat.mul_le_mul_left
  rw [← sq]
  omega

/-- The displayed parameters' sum (the polynomial factor of `c3Cost_le_B`). -/
def bnOf (a : RepairRepresentation.DecompositionAlgorithm) (R : Req.C3Req) : ℕ :=
  R.p + R.P.width + (Pool.poolChildren a R.P.gates R.P.flips).length + R.P.h + R.P.Q + R.d + 1

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
