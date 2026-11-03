import Lean
import Proof.Wire_3_5.FinalPass.Close6
import Proof.Wire_3_5.Primitive.SeedFix.SBId
import Proof.Wire_3_5.Primitive.Writers.SBCap3Base
import Proof.Wire_3_5.Primitive.Writers.SBInstBase
import Proof.Wire_3_5.Primitive.SeedFix.NwB15
import Proof.Wire_3_5.Foundations.OutMachineNwBV
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.UnionMachine.NumsG2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SWParts
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.Primitive.Writers.SBCap3
import Proof.Wire_3_5.Primitive.Writers.SBCost
import Proof.Wire_3_5.Primitive.Writers.SBFieldCost
import Proof.Wire_3_5.Primitive.Writers.SBIdent
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Foundations.OutMachineHUBase
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Foundations.OutMachineNwBVBase
import Proof.Wire_3_5.Foundations.OutMachineSlot0WBase
import Proof.Wire_3_5.Primitive.SeedFix.NwB15Base
import Proof.Wire_3_5.Primitive.SeedFix.SBIdBase
import Proof.Wire_3_5.UnionMachine.NumsG2Base
import Proof.Wire_3_5.UnionMachine.NumsW2Base


noncomputable section
set_option maxRecDepth 120000


/-!
# The final pass's closure join, step 7

`finalPassClose6` with SB and NW supplied by verified code: SB's statements `sbIdent`/`sbOuts`
(T3) and `sbP1Cost`/`sbFieldCost`/`sbCap` (PA2); NW's phase (b) `phB` (T3) over
`needB`/`vLinkB` (X6) at the cells `dX (TW l) (NW l)`, and phase (d) `phD` (X6); and
SW's gate-table part `swG` (C6b). The producers still open are SW's four remaining parts:
`Pt` (top tables), `Pf` (flat tables), `Pl` (templates), `Pn` (numbers).

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Close7

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The final pass from SW's four remaining parts.** -/
noncomputable def finalPassClose7
    (Pt : ∀ l, SWParts.SWtT l) (Pf : ∀ l, SWParts.SWfT l) (Pl : ∀ l, SWParts.SWlT l) (Pn : ∀ l, SWParts.SWnT l) :
    FinalPassStage1.StageT :=
  Close6.finalPassClose6 PrimT.SBId.sbIdent PrimT.SBId.sbOuts (fun l => PrimAsm.SBAsm.sbP1Cost l)
    (fun l => PrimAsm.SBAsm.sbFieldCost l) (fun l => PrimAsm.SBAsm.sbCap l (PrimT.SBId.sbIdent l).starR)
    (fun l => PrimT.ThrDecF.dX (PrimT.ThrDecF.TW l) (PrimT.ThrDecF.NW l))
    (fun l x hx => PrimT.NwB.phB x l hx (Out.NwBV.needB l) (Out.NwBV.vLinkB l)) Out.DPh.phD
    (fun l => UnionMachine.NumsA.swG (UnionMachine.DataDock.DT + 3) le_rfl l) Pt Pf Pl Pn

end NearCubicWires.WireExponent3_5.FinalPass.Close7

end
