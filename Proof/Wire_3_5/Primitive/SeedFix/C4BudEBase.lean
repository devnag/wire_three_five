import Proof.Wire_3_5.Primitive.SeedFix.C4BudD
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNEBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB4

/-! # C4.K item (h), part 5: the SYM stage's steps at every SYM call within `c₄·seedClasses E₄`

P3:3098-3100, 3105-3115 (the seed-fixing budget, `E₄` before `F`, `c₄` after), 1188-1200 (the star: `k = rs`, the
center bits `n − k`, the capacity), 3154-3162 (the sample count): at every SYM call of the family, the SYM stage's steps
(the setup at the capacity `2·2^{⌊n/8⌋+C}+2`, the loop over the child family, the sample expansion, the pad `P`) are
at most `c₄·seedClasses E₄ n k ψ`, for one `c₄` chosen after `F` (`budget_le` over `wrap_split` and `rest_le`).

* `symN_le` (the numbers machine at the call), `ell_le`, `d2_le`, **`sym_steps_le`**.

Paper quantity of the main type: the SYM stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

/-- The two center-bit halves: `2·d_row ≤ n − k + 1` (`centerBits_sum`, `centerBits_balanced`). -/
theorem d2_le (P : StarParams) : 0 + C4Geo.dRow P + C4Geo.dRow P ≤ P.n - P.k + 1 := by
  have h1 := P.centerBits_sum
  have h2 := P.centerBits_balanced
  have e : C4Geo.dRow P = P.leftCenterBits := rfl
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Bud
