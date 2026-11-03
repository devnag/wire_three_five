import Lean
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Wire_3_5.UnionMachine.FrontRest
import Proof.Wire_3_5.UnionMachine.FrontC1D
import Proof.Wire_3_5.UnionMachine.FrontCh5
import Proof.Wire_3_5.UnionMachine.FrontCh3P
import Proof.Wire_3_5.UnionMachine.FrontCallOkBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.UnionMachine.PlanW2Base


noncomputable section
set_option maxRecDepth 4096


/-!
# The union fronts, module stage 1

This module collects the fronts' verified machine block: the decode, the chain's phases 1–5, the atom test and the rest
chain, and C1's call in the front. It proves nothing new: the target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `PlanW3.FrontsFWE3 e l F`, the union machine's fronts (P3:3669-3680).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FrontsStage1

open NearCubicWires.WireExponent3_5

/-- The fronts leaf, unchanged (an alias). -/
abbrev StageT : Type := ∀ l : Literals, Σ e : ℕ, ∀ F : Split.GateFree l, Split.GateFreeOK l F →
  UnionMachine.PlanW3.FrontsFWE3 e l F

/-- The staging step: the leaf from the leaf. -/
def pass (h : StageT) : ∀ l : Literals, Σ e : ℕ, ∀ F : Split.GateFree l, Split.GateFreeOK l F →
    UnionMachine.PlanW3.FrontsFWE3 e l F := h

end NearCubicWires.WireExponent3_5.FrontsStage1

end
