import Proof.Wire_3_5.Primitive.SeedFix.C4KWu
import Proof.Wire_3_5.Primitive.SeedFix.C4KWl
import Proof.Wire_3_5.Primitive.SeedFix.C4KWk
import Proof.Wire_3_5.Primitive.SeedFix.C4KWh
import Proof.Wire_3_5.Primitive.SeedFix.C4KWf

/-! # C4KW: **the kept words writer** `kww : KWW`

The Hb printer's 94 static words before cell `0` (P3:2253-2290), framed, from the call's twelve inputs: the four stages
(B1 the rulers, unary words, constants, registers, log and elimination tapes; B2 the cleared weights' word; B3 the
modulus word; B4 the framed HASH tape and populations) composed (`Cmp.kwwOf`). The HASH setup docks it (T-b,
`KwDock`); the c4 finish term `C4HL.c4Leaf_of_obl2` takes it as `Wk`.

Paper quantity of the main type: the Hb printer's static words at the HASH call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW

/-- **The kept words writer.** -/
noncomputable def kww : KWW := Cmp.kwwOf B1.partB1 B2.partB2 partB3 partB4

end NearCubicWires.WireExponent3_5.PrimT.C4KW
