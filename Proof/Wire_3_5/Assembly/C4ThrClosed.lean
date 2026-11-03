import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4LeafA
import Proof.Wire_3_5.Primitive.Writers.ThrLf2
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Bindings.Williams14_Corollary4_4
import Proof.Wire_3_5.Assembly.C4SymClosedBase
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.Writers.ThrB7Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.Primitive.Writers.ThrDataH
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base
import Proof.Wire_3_5.Primitive.Writers.ThrStrip7
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4WBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The c4 leaf with its SYM and THR modes closed (root dock)

`C4LeafA.c4Leaf_of3` assembles the seed-fixing leaf from the THR and HASH modes, with the SYM mode already
closed by `C4SymClosed.symLeafClosed` at the Williams algorithm `waOf l` chosen from the williams literal. The THR mode is
the `ThrLf.thrLeafC4`, a verified producer. This dock checks that it plugs in, so the c4 leaf is a
function of the HASH mode alone.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4ThrClosed

open NearCubicWires.WireExponent3_5

/-- **The c4 leaf from its HASH mode alone** (SYM and THR supplied by verified producers). -/
noncomputable def c4Leaf_of_hash (hH : ∀ l : Literals, PrimT.C4K.HashLeafC4 l) (l : Literals) :
    PrimT.SeedFixTypes.C4Leaf l :=
  PrimT.C4LeafA.c4Leaf_of3 l (PrimAsm.ThrLf.thrLeafC4 l (PrimT.C4LeafA.waOf l)) (hH l)

end NearCubicWires.WireExponent3_5.C4ThrClosed

end
