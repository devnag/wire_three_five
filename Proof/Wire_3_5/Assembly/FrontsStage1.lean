import Proof.Wire_3_5.UnionMachine.FrontCallOk
import Proof.Wire_3_5.UnionMachine.FrontRest

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FrontsStage1

open NearCubicWires.WireExponent3_5

/-- The fronts leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, Σ e : ℕ, ∀ F : Split.GateFree l, Split.GateFreeOK l F →
  UnionMachine.PlanW3.FrontsFWE3 e l F

def pass (h : StageT) : ∀ l : Literals, Σ e : ℕ, ∀ F : Split.GateFree l, Split.GateFreeOK l F →
    UnionMachine.PlanW3.FrontsFWE3 e l F := h

end NearCubicWires.WireExponent3_5.FrontsStage1
