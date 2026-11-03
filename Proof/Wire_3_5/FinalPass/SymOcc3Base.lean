import Proof.Wire_3_5.FinalPass.SymOcc2

/-! # The printer's gate budget at a SYM call, part 3: `occ_sym`

At a SYM call of the gate, with the floors (`occCD ≤ C_D`, `1 ≤ c_ψ`; P3:3094-3107, "C_D sufficiently large"),
the child request of every prefix meets alg:eq-budget's clause of `C3Req.Pre` (P3:1897-1900) at the free numbers
`freeVal2 (symK2 c)` and the degree `symDF c`: the dense pool is below `2^{k + cDa·L}` (**`symD_le`**), the expression
below `2^{A₁(k+L)}` (a premise, from the batch's shape), `m ≤ 400(k+L)`, `Q' = dQ(k+L)`, `d = dD(⌊√B_S⌋+L)`; the
linear part is within `C_D(k+L) ≤ ψ` and the quadratic part within `C_D²(k+L)²(⌊√B_S⌋+L) ≤ ψ`.
* `occCD`, **`symD_le`**, **`occ_sym`**.
Paper quantities of the main types: alg:eq-budget at a SYM call against the load `ψ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine

/-- **The load-constant floor of the printer's budget** (chosen before `F`: the algorithm is the literals'). -/
def occCD (a : RepairRepresentation.DecompositionAlgorithm) (c : SymC) (A1 : ℕ) : ℕ :=
  160 * (A1 + 400 + c.dQ + 1) + 160 * (c.dQ * c.dD * cDa a) + 2

theorem symBud_le' (a : RepairRepresentation.DecompositionAlgorithm) (n : ℕ) :
    symBud a n ≤ a.coefficient * 4 ^ a.degree * (n + 1) ^ (26 * a.degree) := by
  unfold symBud
  have h1 : n + ((n + 1) ^ 26 + 2) + 1 ≤ 4 * (n + 1) ^ 26 := by
    have : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    omega
  calc a.coefficient * (n + ((n + 1) ^ 26 + 2) + 1) ^ a.degree
      ≤ a.coefficient * (4 * (n + 1) ^ 26) ^ a.degree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

