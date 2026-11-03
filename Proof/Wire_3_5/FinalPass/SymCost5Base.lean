import Proof.Wire_3_5.FinalPass.SymCost4Base

/-! # The SYM child's cost, part 5: the pad over the family's cell (`hR`)

P3:3098-3100 (the pad `2^ρ`, `ρ = max(n − 2k_h + d_Aβ, d_Rβ²)`): the child family's loop cell at cost `2K_ch + 2`
(`K_ch = symKch = 2^{n − k + d_A L − 4}`, the comparison at the sum's width `W = Q' + 2dRow + 2(p+1) + 4` and the
`8ℓ` decisions) fits the pad: `(2K_ch+2) + 1 + ((2K_ch+2) + 1 + (2·cmpCost W 0^{8ℓ} + 2)) + 1 ≤ 2^ρ`. The cell is
`4K_ch + 146W + 80ℓ + 79`; `4K_ch = 2^{n−k+d_A L−2}` and `146W + 80ℓ + 79 ≤ 2^{e_X + 11} ≤ 2^{n−k+d_A L−2}`
(`kch_exp` (1)). This is SymEAt3's (and v7's SymPadEAt's) `hR` at the family's explicit cell cost.

* `cmpCost_eq`, **`symHR`**.

Paper quantity of the main type: the SYM loop cell's steps against the pad. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.RepairRepresentation

theorem cmpCost_eq (W : ℕ) (p : List Bool) : PrimT.C4Loop.cmpCost W p = 73 * W + 5 * p.length + 35 := by
  unfold PrimT.C4Loop.cmpCost; omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
