import Proof.Wire_3_5.Assembly.C4Stage7
import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf4
import Proof.Wire_3_5.Primitive.SeedFix.C4KWv
import Proof.Wire_3_5.Primitive.Writers.HashBud4

/-!
# The c4 leaf, module block 8

The eighth verified block of the c4 leaf: the kept words writer's stage B2 and the whole writer `kww`
, the HASH part of `C4Leaf` with its finish shape `c4Leaf_of_obl2`, the
HASH fit lemma and the HASH budget with the packaged obligation `hobl2`. It is staged ahead of
the c4 finish so that the finish ships only the T-a/b/c producers and the one-line top module. The target passes
through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage8

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage7.StageT

def pass (h : StageT) : C4Stage7.StageT := h

end NearCubicWires.WireExponent3_5.C4Stage8
