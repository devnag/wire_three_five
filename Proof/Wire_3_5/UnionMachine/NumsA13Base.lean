import Proof.Wire_3_5.UnionMachine.NumsA6Base

/-! # NW phase (a), part 13 (build once): the SYM numbers' full register export

For the shared `symFront` (SWf, SWl, SWn) and NW's (a): the SYM numbers program at a SYM request, the WHOLE block
`G` (`numsVec` at the call's numbers), `dN = n`, `dM_j = |symGates C_j|` (`0` past `a`), `KB 52 = Q`, every register
`≤ cap₀`; on the `x = 0` bank (`numsAtG`) and lifted onto NW's bank (`numsBankG`). Identification of the block's list
entries with `symListParams` (`G 32 = M`, `G 33 = B`, `G 34 = errExp`, `G 41 = |FlatSeed|`) and of `dM_j`.

* **`numsAtG`**, **`numsBankG`**, `numsVec_32`, `numsVec_33`, `numsVec_34`, `numsVec_41`, **`ident_M`**,
  **`ident_B`**, **`ident_err`**, **`ident_flat`**, **`cy_getD_len`**.

Paper quantities of the main type: the SYM call's numbers (`|FlatSeed|`, the list parameters `M, B, errExp`, the
bottom counts `|G_j|`, `Q`) in registers (P3:2929-2941, 2994-3000, 3011-3016). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Vec


end Vec

section Gate
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

section Ident

end Ident

/-- `dM_j = |symGates C_j|` below `a`. -/
theorem cy_getD_len {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (j : ℕ) (h : j < a') :
    (SymDec.cyOf Cs).getD j 0 = (Stars.symGates (Cs ⟨j, h⟩)).length := by
  unfold SymDec.cyOf
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
