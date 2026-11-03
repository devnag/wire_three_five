import Proof.Wire_3_5.FinalPass.SymCap2Base
import Proof.Wire_3_5.FinalPass.SymOcc3Base
import Proof.Wire_3_5.Primitive.SeedFix.C4PadA

/-! # The SYM enumeration's capacity, part 3: `EnumOk` at every SYM call

P3:3011-3016, 2987-2988 at a SYM call, with the free numbers `TWd = d_T L²`, `Cap = 2^{⌊n/16⌋ + d_C L²}` (the v2
program) and the cell cost bound `K(n) = 2^{⌊n/16⌋ + d_C L²}`: `n_T ≤ 2^{TWd}` (`2e_N ≤ d_T`), `Q ≥ 1`, and the group
size bound `capC·(qG(8ℓ)+1)^6 ≤ Cap` under the load floor `16·symC1 ≤ C_D` (with `1 ≤ c_ψ`: `ψ ≤ n`) and
`symDC ≤ d_C`; so the enumeration's hypotheses hold at every child prefix (the generic `EnumCap.enumOk_of`, SYM as one
instance). Also `Q' ≤ pr` and `1 ≤ h` at the call.

* `symKn`, **`hnT_sym`**, **`hQ_sym`**, `hQp_sym`, `one_le_h_sym`;
* **`symQ_of`**, **`symHok_of`** (generic in the call's batch, `R ≤ 10`, the degree bound `D`), their instances
  **`symQ_le`**, **`symHok`** (the SYM batch, `D = symDg`) and **`padHok`** (the degenerate call's padded batch,
  `R′ = 1`, `D = 0`; v7's `SymPadEAt.hok`).

Paper quantity of the main type: the enumeration's hypotheses at a SYM call's child prefixes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

/-- The cell cost bound `K(n) = 2^{⌊n/16⌋ + d_C L²}` (the capacity's value). -/
def symKn (c : SymC) (n : ℕ) : ℕ := 2 ^ (n / 16 + c.dC * (Nat.clog 2 (n + 2) * Nat.clog 2 (n + 2)))

section Gate
variable (l : Literals) 

/-- `1 ≤ h` at a SYM call (`1 ≤ d_H`). -/
theorem one_le_h_sym (c : SymC) (hdH : 1 ≤ c.dH) (x : FreeIn) : 1 ≤ (freeProg2 (symK2 c)).val x 3 := by
  show 1 ≤ c.dH * (x.n + 1) ^ c.eH
  exact Nat.mul_le_mul hdH (Nat.one_le_pow _ _ (by omega))

/-- The constant row's word. -/
theorem constRow_word : (ListMachine.Rec.exprWord PrimT.C4Pad.constRow).length ≤ 2 ^ 24 := by decide

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
