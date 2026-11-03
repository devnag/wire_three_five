import Lean
import Proof.Wire_3_5.Foundations.OutMachineHU
import Proof.Wire_3_5.Foundations.OutMachineSlot0W
import Proof.Wire_3_5.Primitive.Writers.SBInst
import Proof.Wire_3_5.UnionMachine.NumsW2
import Proof.Wire_3_5.FinalPass.SWParts
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreJ11
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.Primitive.Writers.SBIdent
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Primitive.Writers.SBTypes2
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.Foundations.OutMachineHUBase
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase
import Proof.Wire_3_5.Primitive.Writers.SBInstBase
import Proof.Wire_3_5.UnionMachine.NumsW2Base


noncomputable section
set_option maxRecDepth 120000


/-!
# The final pass's closure join, step 6

X6's `finalPassClose5` (the final pass from the four pool writers, with the uniformity bundle `hU4` supplied,
) at the four writers assembled from verified code: SA = `SA.sa` (complete); SB = PA2's
`sbWriter` over its five arithmetic statements; NW = the `nwOf` at the cells `xNW db l` over
its phases (b) and (d); SW = the `swOf` over its five parts. The producers still open, one binder
each: SB's statements `hI hO hC hF hK`; NW's phase (b) `pb` (T3) and phase (d) `pd` (X6) with (b)'s cell bound
`db`; SW's parts `Pg Pt Pf Pl Pn` (C6b, C1b).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close6

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The final pass from exactly its remaining open producers.** -/
noncomputable def finalPassClose6
    (hI : ∀ l, PrimAsm.SBIdent.SBIdentStmts l) (hO : ∀ l, PrimAsm.SBTypes.SBOutsStmt l)
    (hC : ∀ l, PrimAsm.SBTypes.SBCostStmt l) (hF : ∀ l, PrimAsm.SBAsm.SBFieldCostStmt l)
    (hK : ∀ l, PrimAsm.SBTypes.SBCapStmt l)
    (db : Literals → ℕ) (pb : ∀ l x, db l ≤ x → UnionMachine.NumsPh3.PhB x l)
    (pd : ∀ x, UnionMachine.NumsPh4.PhD' x)
    (Pg : ∀ l, SWParts.SWgT l) (Pt : ∀ l, SWParts.SWtT l) (Pf : ∀ l, SWParts.SWfT l) (Pl : ∀ l, SWParts.SWlT l)
    (Pn : ∀ l, SWParts.SWnT l) :
    FinalPassStage1.StageT :=
  Out.HU.finalPassClose5 fun l =>
    { SA := Out.SA.sa l
      SB := PrimAsm.SBAsm.sbWriter l (hI l) (hO l) (hC l) (hF l) (hK l)
      NW := UnionMachine.NumsA.nwOf l (UnionMachine.NumsA.xNW db l) (UnionMachine.NumsA.xNW_a db l)
        (pb l _ (UnionMachine.NumsA.xNW_b db l)) (pd _)
      SW := SWParts.swOf (Pg l) (Pt l) (Pf l) (Pl l) (Pn l) }

end NearCubicWires.WireExponent3_5.FinalPass.Close6

end
