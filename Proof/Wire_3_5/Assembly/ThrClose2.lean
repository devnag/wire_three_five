import Proof.Wire_3_5.Assembly.ThrClose
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ10

/-!
# The thr leaf's closure join, step 2

`thrClose` with the unit cells and the decode fronts supplied by verified code: the cells
`xT l F = max walkBank.x (dX …)` with `xT_walk`, and the decode fronts as a uniform family `decT`. The one
producer still open:

* `tail`: THRTAIL, the THR writer's leaf from the unit machines v4 (T-A = `ThrDimB.thrDimStageG`; T-B, the
  shell run and class link; the dock `thrLeafOfU4_of`), with the pre-link available.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3011-3016,
3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrClose2

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The thr leaf from exactly its remaining open producer**, THRTAIL. -/
noncomputable def thrClose2
    (tail : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → UnionMachine.ThrUnit.ThrLeafOfU4 l) :
    ThrStage3.StageT :=
  ThrClose.thrClose tail PrimT.ThrDecF.xT PrimT.ThrDecF.xT_walk PrimT.ThrDecF.decT

end NearCubicWires.WireExponent3_5.ThrClose2
