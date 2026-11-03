import Lean
import Proof.Wire_3_5.Assembly.C4Stage2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymND4
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4GrpD
import Proof.Wire_3_5.Primitive.SeedFix.C4PadC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC
import Proof.Wire_3_5.Primitive.Writers.SFCost5
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.Primitive.Writers.ThrStage2
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The c4 leaf, module block 3

The third verified block of the c4 leaf: the SYM side conditions' machinery at capacity v2 (contract v5, `sym_bigS2`,
`sym_hc3`), the degenerate-call branch `padStage` and the group lemmas, the SeedFix cost bounds and the C3 request
writer v3. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage3

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage2.StageT

end NearCubicWires.WireExponent3_5.C4Stage3

end
