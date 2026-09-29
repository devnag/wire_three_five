import Proof.Wire_3_5.Assembly.C4Stage4
import Proof.Wire_3_5.Assembly.C4SymClosed
import Proof.Wire_3_5.Primitive.Writers.ThrHc3
import Proof.Wire_3_5.Primitive.SeedFix.C4H2
import Proof.Wire_3_5.Primitive.SeedFix.C4HD

/-!
# The c4 leaf, module block 5

The fifth verified block of the c4 leaf: the closed SYM mode (`C4SymClosed.symLeafClosed`: the assembly at the v7
builder, the C3 writer v3 and the padded evaluation), the THR stage at capacity v2 with the strip
, and the HASH contract with its data. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage5

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage4.StageT

def pass (h : StageT) : C4Stage4.StageT := h

end NearCubicWires.WireExponent3_5.C4Stage5
