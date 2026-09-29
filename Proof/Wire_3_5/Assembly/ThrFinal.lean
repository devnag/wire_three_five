import Proof.Wire_3_5.Assembly.ThrStage4
import Proof.Wire_3_5.Primitive.SeedFix.ThrTB8

/-!
# The thr leaf

The THR writer's leaf at every literal instance: root's closure join `thrClose2` (the verified decode fronts `decT` at
the cells `xT`, the unit machines `thrUnitOf5` over the RADIX setups `radStage`, the FILTER setup `fsSpec` at the walk
bank, the v4 data stage `thrStage4U`) applied to THRTAIL's `tail`: the shell run over the dimension stage with the bounds (`thrDimStageG`), the class link into the preprocessing class, and the v4 dock.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}`
(P3:3011-3016, 3094-3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrFinal

open NearCubicWires.WireExponent3_5

/-- **The thr leaf** at every literal instance. -/
noncomputable def thrFinal : ThrStage4.StageT :=
  ThrClose2.thrClose2 PrimT.ThrTB.tail

end NearCubicWires.WireExponent3_5.ThrFinal
