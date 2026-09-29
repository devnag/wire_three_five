import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.AssemblyDock

/-! # The final pass's assembly dock, v2: S4's words with the filter's parameters

`AssemblyDock` composes the phases over `SeedsProg3` (at `frontWordsW`). Since S4
receives `frontWordsW2` (slot `7` with the filter's parameters): this is its twin over `SeedsProg3`, the front phase
carrying the width bound `W r ≤ Cw·(|fpIn|+1)^{Dw}` (from `S5CoreB3`) for S6.

* **`FrontPh2 Y`**: the front phase on S4's layout at `frontWordsW2`, its cost within `s5Bound Cf Df`, its width
  bound; `LayExt3`, `layOf3` (the halves' `S5Lay` at S4's layout);
* `seedsPh3`, `numDen3`, `two_le_t3`, `phasesOf3`, `phasesOf3_fits` (`fits_of`), and **`finalPass_of2`** (`fpPlan`).

Paper quantity of the main type: the final pass's leaf `FinalPassLeaf l` (the primitive's printed value within
`c₅·finalClasses`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Assembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Assembly
