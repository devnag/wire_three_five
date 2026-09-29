import Proof.Wire_3_5.Assembly.C4Stage2
import Proof.Wire_3_5.Primitive.SeedFix.C4GrpD
import Proof.Wire_3_5.Primitive.SeedFix.C4PadC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymHc
import Proof.Wire_3_5.Primitive.SeedFix.C4SymND4
import Proof.Wire_3_5.Primitive.Writers.C3W3Leaf
import Proof.Wire_3_5.Primitive.Writers.SFCost5

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage3

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage2.StageT

end NearCubicWires.WireExponent3_5.C4Stage3
