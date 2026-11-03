import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeaf
import Proof.Wire_3_5.Assembly.C4SymClosed
import Bindings.Williams14_Corollary4_4
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Assembly.C4SymClosedBase
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase


noncomputable section
set_option maxRecDepth 4096


/-! # C4Leaf, the assembly: the C4 part from the three modes' stages

P3:3105-3115, 3165-3175 (the seed-fixing stage of `lem:primitive`: the fixed seeds within `c₄·seedClasses E₄`). The
C4 part `C4Leaf l` is C4.K's `c4Leaf_of` at the three modes' stages: SYM from root's closed dock
`C4SymClosed.symLeafClosed` (verified producers only), THR (the `ThrLeafC4`) and HASH (`HashLeafC4`). The printer's
Williams algorithm `wa` is picked by `Classical.choice` from the williams literal (`Literals.williams` through the
binding `Williams14.williams14_to_import`); no machine reads the choice beyond the printer the literal provides.

* `waOf`, **`c4Leaf_of3`**.

Paper quantity of the main type: the C4 part `C4Leaf l`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4LeafA
open NearCubicWires NearCubicWires.WireExponent3_5

/-- **The printer's algorithm**, picked by `Classical.choice` from the williams literal. -/
noncomputable def waOf (l : Literals) : RepairRepresentation.WilliamsAlgorithm :=
  Classical.choice (Bindings.Williams14.williams14_to_import l.williams)

/-- **The C4 part** from the THR and HASH stages (the SYM stage is root's closed dock at `waOf l`). -/
noncomputable def c4Leaf_of3 (l : Literals) (hT : C4K.ThrLeafC4 l) (hH : C4K.HashLeafC4 l) : SeedFixTypes.C4Leaf l :=
  C4K.c4Leaf_of l (C4SymClosed.symLeafClosed l (waOf l)) hT hH

end NearCubicWires.WireExponent3_5.PrimT.C4LeafA

end
