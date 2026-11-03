import Lean
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ9
import Proof.Wire_3_5.UnionMachine.WalkStage
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.UnionMachine.ThrDecIface
import Proof.Wire_3_5.UnionMachine.ThrUnitIface
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ9Base


noncomputable section
set_option maxRecDepth 120000


/-! # T3 THR decode front, packaging part 10: the decode fronts at the thr closure's cells

The thr closure join (`ThrClose.thrClose tail xF hx dec`) takes the unit cells `xF` with
`walkBank.x ≤ xF l F` and the decode fronts `dec` as a uniform family at `xF`. **`xT l F = max walkBank.x (dX (TW l)
(NW l))`** satisfies both (`xT_walk`, `xT_dec`); **`decT`** is `dec` at `xT`, and **`decOf`** is `dec` at any cells
above `dX (TW l) (NW l)`.

Paper quantity of the main type: the THR call's rows at each unit of the THR tape (P3:2543-2558, 2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- The unit cells: the walk bank's streams and the decode front's scratch. -/
noncomputable def xT (l : Literals) (F : GateFree l) : ℕ :=
  max UnionMachine.WalkStage.walkBank.x (dX (TW l) (NW l))

theorem xT_walk (l : Literals) (F : GateFree l) : UnionMachine.WalkStage.walkBank.x ≤ xT l F := le_max_left _ _

theorem xT_dec (l : Literals) (F : GateFree l) : dX (TW l) (NW l) ≤ xT l F := le_max_right _ _

/-- **The decode fronts at any cells above `dX`**, in `ThrClose.thrClose`'s `dec` binder type. -/
noncomputable def decOf (xF : ∀ l : Literals, GateFree l → ℕ) (h : ∀ (l : Literals) (F : GateFree l), dX (TW l) (NW l) ≤ xF l F) :
    ∀ l : Literals, FinalPass.Seams.StageU l (fun F _ _ _ _ _ => UnionMachine.ThrDec.ThrDecFront (xF l F) l F)
      (fun D => UnionMachine.ThrUnit.decDeg D) (fun D => UnionMachine.ThrUnit.decCf D) :=
  fun l => thrDecU l (xF l) (h l)

/-- **The decode fronts at `xT`**, `ThrClose.thrClose`'s `dec` at `xF = xT`. -/
noncomputable def decT : ∀ l : Literals, FinalPass.Seams.StageU l (fun F _ _ _ _ _ => UnionMachine.ThrDec.ThrDecFront (xT l F) l F)
    (fun D => UnionMachine.ThrUnit.decDeg D) (fun D => UnionMachine.ThrUnit.decCf D) :=
  decOf xT xT_dec

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF

end
