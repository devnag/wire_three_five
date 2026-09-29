import Proof.Wire_3_5.Assembly.C4Stage8
import Proof.Wire_3_5.Primitive.Writers.HashBud5
import Proof.Wire_3_5.Primitive.Writers.TProdAll

/-!
# The c4 leaf

The seed-fixing stage's leaf at every literal instance: `c4Leaf_of_obl3` (the SYM and THR modes, closed at root,
with the HASH mode) applied to the kept words writer `kww` (…), the T-a/b/c producers
and the packaged HASH obligation `hobl3` (fits, budget /m67).

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Final

open NearCubicWires.WireExponent3_5

/-- **The c4 leaf** at every literal instance. -/
noncomputable def c4Final : C4Stage8.StageT :=
  PrimT.C4HL.c4Leaf_of_obl3 PrimT.C4KW.kww (PrimAsm.TProd.tA PrimT.C4KW.kww) (PrimAsm.TProd.tB PrimT.C4KW.kww)
    (PrimAsm.TProd.tC PrimT.C4KW.kww) (PrimAsm.HashBud.hobl3 PrimT.C4KW.kww)

end NearCubicWires.WireExponent3_5.C4Final
