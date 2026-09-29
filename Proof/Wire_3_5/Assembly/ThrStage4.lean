import Proof.Wire_3_5.Assembly.ThrClose2
import Proof.Wire_3_5.UnionMachine.ThrDimG

/-!
# The thr leaf, module stage 4

The fourth verified block of the thr leaf, shipped ahead of its finish: the completed THR decode front (ThrDecQ1–Q10:
the quasi calculus, the call atoms, the front's cost, the index links, `thrDecFront` and the uniform family `decT` at
the cells `xT`), the THR dimension-stage bounds (ThrDimM/N/C/G, `thrDimStageG`), and the closure join `thrClose2`
(its one open argument is the THR writer's tail). The finish then ships only the tail (the shell run, the class link
and the v4 dock) and the instantiation of `thrClose2`. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: the THR tape `thrTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}`
(P3:3011-3016, 3108, 3112-3114).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ThrStage4

open NearCubicWires.WireExponent3_5

/-- The thr leaf, unchanged (an alias). -/
abbrev StageT : Type := ThrStage3.StageT

def pass (h : StageT) : ThrStage3.StageT := h

end NearCubicWires.WireExponent3_5.ThrStage4
