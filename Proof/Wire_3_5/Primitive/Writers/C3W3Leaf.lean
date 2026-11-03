import Lean
import Proof.Wire_3_5.Primitive.Writers.C3W3Budget
import Proof.Wire_3_5.Primitive.Writers.C3ReqIface3
import Proof.Wire_3_5.Primitive.Writers.C3WLeaf
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetA
import Proof.Wire_3_5.Primitive.Writers.C3WCall
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface


noncomputable section
set_option maxRecDepth 4096


/-! # PA2: the C3 request writers at the polynomial load premise (`C3ReqIface3.C3ReqLeaf3`)

The writers (`C3Leaf.c3At`, the same stages and runs) with the budget at the premise
`h + Q' + m + pr ≤ c_N·(Ψ+1)·(n+1)^{D_N}` (`C3Cost.call_budget3`): **`c3At3`**, **`c3ReqLeaf3`** (envelope
`EW3 l D_N`, `CD_W = 1`, coefficient `cWF l c_N c_r` as before).

Paper quantities of the main type: the compiler's fixed fields `preW`/`postW` of the call's request within the
preprocessing class (P3:3108, 3170-3173), at a pool whose coefficients need `poly(n)` bits (alg:disjoint). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Leaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.CompilerMachine

section At
variable (l : Literals) (F : GateFree l) (cN kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The C3 request writers at one call family, at the polynomial load premise.** -/
noncomputable def c3At3 (DN : ℕ) (hCD : 1 ≤ F.CD) :
    C3ReqIface3.C3ReqAt3 l F (C3Cost.EW3 l DN) (cWF l cN (gate0 l F).row.cr) cN DN kclk coef A a ha where
  sym := (wr5 l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha (gsAt l F kclk coef A a ha).toWriterStage
    (sAt l F kclk coef A a ha) (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha)).stage DvC
    (CvF (gate0 l F).row.cr) (C3a.Lay.c3aM (gate0 l F).alg) (c3aIn (gate0 l F).alg) (C3a.Word.c3aOut (gate0 l F).alg)
  sym_run := fun n a' ha' Cs carriers translation hcall hs h Q m pr hh hfit hhQ => by
    have hG := (gsAt l F kclk coef A a ha).ready n a' ha' Cs carriers translation hcall hs
    have sz := call_sizes l F kclk coef A a ha (gsAt l F kclk coef A a ha).toWriterStage (sAt l F kclk coef A a ha)
      (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha) (symReq n a' ha' Cs carriers translation) hcall hs
      (Records.symPool Cs carriers) _ hG
    rw [classBound_EGp] at sz
    exact call_run l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha (gsAt l F kclk coef A a ha).toWriterStage
      (sAt l F kclk coef A a ha) (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha) DvC (CvF (gate0 l F).row.cr)
      (symReq n a' ha' Cs carriers translation) hcall hs (Records.symPool Cs carriers) _ hG h Q m pr hh hfit
      (call_hpoly l F kclk coef A a ha (symReq n a' ha' Cs carriers translation) hs (Records.symPool Cs carriers)
        PrimT.C4GateSym.gsD cGg gsD_le (by omega) sz.1 sz.2.1 sz.2.2) _
      (call_budget3 l F kclk coef A a ha DN (gsAt l F kclk coef A a ha).toWriterStage (sAt l F kclk coef A a ha)
        (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha) (symReq n a' ha' Cs carriers translation) hcall hs
        (Records.symPool Cs carriers) _ hG PrimT.C4GateSym.gsD cGg gsD_le (by omega) (by rw [classBound_EGp])
        h Q m pr hh hfit cN hhQ hCD)
  thr := (wr5 l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha (gtAt l F kclk coef A a ha).toWriterStage
    (sAt l F kclk coef A a ha) (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha)).stage DvC
    (CvF (gate0 l F).row.cr) (C3a.Lay.c3aM (gate0 l F).alg) (c3aIn (gate0 l F).alg) (C3a.Word.c3aOut (gate0 l F).alg)
  thr_run := fun n a' ha' Cs carriers translation hcall hs h Q m pr hh hfit hhQ => by
    have hG := (gtAt l F kclk coef A a ha).ready n a' ha' Cs carriers translation hcall hs
    have sz := call_sizes l F kclk coef A a ha (gtAt l F kclk coef A a ha).toWriterStage (sAt l F kclk coef A a ha)
      (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha) (thrReq n a' ha' Cs carriers translation) hcall hs
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) _ hG
    rw [classBound_EGp] at sz
    exact call_run l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha (gtAt l F kclk coef A a ha).toWriterStage
      (sAt l F kclk coef A a ha) (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha) DvC (CvF (gate0 l F).row.cr)
      (thrReq n a' ha' Cs carriers translation) hcall hs
      (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) _ hG h Q m pr hh hfit
      (call_hpoly l F kclk coef A a ha (thrReq n a' ha' Cs carriers translation) hs
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)
        (PrimT.C4GateSym.gtD PrimAsm.ThrData.thrDataStage2) cGt gtD_le (by omega) sz.1 sz.2.1 sz.2.2) _
      (call_budget3 l F kclk coef A a ha DN (gtAt l F kclk coef A a ha).toWriterStage (sAt l F kclk coef A a ha)
        (wAt l F kclk coef A a ha) (cAt l F kclk coef A a ha) (thrReq n a' ha' Cs carriers translation) hcall hs
        (Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers) _ hG
        (PrimT.C4GateSym.gtD PrimAsm.ThrData.thrDataStage2) cGt gtD_le (by omega) (by rw [classBound_EGp])
        h Q m pr hh hfit cN hhQ hCD)

end At

/-- **The C3 request writers' deliverable at the polynomial load premise** (`C3ReqIface3.C3ReqLeaf3`): after
`c_N`, `D_N` and `fe`, the floors `EW3 l D_N` and `C_D ≥ 1`; for every admissible `F`, the coefficient
`cWF l c_N c_r` and the writers at every clock and source work. -/
noncomputable def c3ReqLeaf3 (l : Literals) : C3ReqIface3.C3ReqLeaf3 l := fun cN DN _fe =>
  ⟨C3Cost.EW3 l DN, 1, fun F _ _ hCD => ⟨cWF l cN (gate0 l F).row.cr, fun kclk coef A a ha =>
    c3At3 l F cN kclk coef A a ha DN hCD⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.C3Leaf

end
