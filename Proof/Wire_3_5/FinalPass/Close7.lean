import Proof.Wire_3_5.FinalPass.Close6
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.Foundations.OutMachineNwBV
import Proof.Wire_3_5.Primitive.SeedFix.NwB15
import Proof.Wire_3_5.Primitive.SeedFix.SBId
import Proof.Wire_3_5.Primitive.Writers.SBCap3
import Proof.Wire_3_5.UnionMachine.NumsG2

/-!
# The final pass's closure join, step 7

`finalPassClose6` with SB and NW supplied by verified code: SB's statements `sbIdent`/`sbOuts`
and `sbP1Cost`/`sbFieldCost`/`sbCap`; NW's phase (b) `phB` over
`needB`/`vLinkB` (the output machine) at the cells `dX (TW l) (NW l)`, and phase (d) `phD` (the output machine); and
SW's gate-table part `swG`. The producers still open are SW's four remaining parts:
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
