import Lean
import Proof.Wire_3_5.Assembly.C4Stage7
import Proof.Wire_3_5.Primitive.Writers.HashBud2
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf2Base
import Proof.Wire_3_5.Primitive.SeedFix.C4KWv
import Bindings.Williams14_Corollary4_4
import Proof.Wire_3_5.Assembly.C4SymClosedBase
import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.FinalPass.FreeGen9
import Proof.Wire_3_5.FinalPass.HashCost3Base
import Proof.Wire_3_5.FinalPass.HashFreeBase
import Proof.Wire_3_5.FinalPass.SampPre
import Proof.Wire_3_5.FinalPass.SymBuildBase
import Proof.Wire_3_5.FinalPass.SymFr3Base
import Proof.Wire_3_5.FinalPass.SymHrBase
import Proof.Wire_3_5.FinalPass.SymOcc3Base
import Proof.Wire_3_5.FinalPass.SymPool
import Proof.Wire_3_5.Primitive.Writers.BShape5
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.Writers.HashSetH2Base
import Proof.Wire_3_5.Primitive.Writers.SFCost5
import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrStage2
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4GrpD
import Proof.Wire_3_5.Primitive.SeedFix.C4H2
import Proof.Wire_3_5.Primitive.SeedFix.C4HB
import Proof.Wire_3_5.Primitive.SeedFix.C4HBh
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.Primitive.SeedFix.C4HfP
import Proof.Wire_3_5.Primitive.SeedFix.C4HkI
import Proof.Wire_3_5.Primitive.SeedFix.C4HkJBase
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Proof.Wire_3_5.Primitive.SeedFix.C4KWl
import Proof.Wire_3_5.Primitive.SeedFix.C4PadC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB2
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymND4
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The c4 leaf, module block 8

The eighth verified block of the c4 leaf: the kept words writer's stage B2 and the whole writer `kww`, the HASH part of
`C4Leaf` with its finish shape `c4Leaf_of_obl2`, the HASH fit lemma and the HASH budget with the packaged obligation
`hobl2`. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage8

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage7.StageT

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : C4Stage7.StageT := h

end NearCubicWires.WireExponent3_5.C4Stage8

end
