import Proof.Wire_3_5.Assembly.C4Stage5
import Proof.Wire_3_5.Assembly.C4ThrClosed
import Proof.Wire_3_5.FinalPass.HashFreeBuild
import Proof.Wire_3_5.Primitive.SeedFix.C4HkJ

/-!
# The c4 leaf, module block 6

The sixth verified block of the c4 leaf: the closed THR mode (`C4ThrClosed.c4Leaf_of_hash`, `thrLeafC4`,
…), the HASH child family and its docking, finisher and uniform stage (…), the
Hb printer's bounds, and the HASH side-condition builder (…). The target passes through
unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage6

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage5.StageT

def pass (h : StageT) : C4Stage5.StageT := h

end NearCubicWires.WireExponent3_5.C4Stage6
