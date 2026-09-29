import Proof.Wire_3_5.Assembly.C4Stage1
import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.Primitive.SeedFix.C4SymND
import Proof.Wire_3_5.Primitive.Writers.ThrStage2

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage2

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage1.StageT

end NearCubicWires.WireExponent3_5.C4Stage2
