import Lean
import Proof.Wire_3_5.Assembly.C4Stage4
import Proof.Wire_3_5.Assembly.C4SymClosedBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4H2
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.FinalPass.FreeGen9
import Proof.Wire_3_5.FinalPass.SampPre
import Proof.Wire_3_5.FinalPass.SymFr3Base
import Proof.Wire_3_5.FinalPass.SymHrBase
import Proof.Wire_3_5.FinalPass.SymOcc3Base
import Proof.Wire_3_5.FinalPass.SymPool
import Proof.Wire_3_5.Primitive.Writers.BShape5
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.Writers.SFCost5
import Proof.Wire_3_5.Primitive.Writers.ThrStage2
import Proof.Wire_3_5.Primitive.SeedFix.C4GrpD
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Proof.Wire_3_5.Primitive.SeedFix.C4PadC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymND4
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The c4 leaf, module block 5

The fifth verified block of the c4 leaf: the closed SYM mode (`C4SymClosed.symLeafClosed`: the assembly at the v7
builder, the C3 writer v3 and the padded evaluation), the THR stage at capacity v2 with the strip, and the HASH contract
with its data. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage5

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage4.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : C4Stage4.StageT := h

end NearCubicWires.WireExponent3_5.C4Stage5

end
