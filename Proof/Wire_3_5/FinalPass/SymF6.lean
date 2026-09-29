import Proof.Wire_3_5.FinalPass.SymF5
import Proof.Wire_3_5.FinalPass.TabShell

/-! # SWf (the SYM words writer's flat tables), part 6: the writer run (the THR shell, P3:1508-1520)

The flat tables writer is the THR writer shell over the data stage v2 with the empty THR tuple (as S4's tables
writer `TabW.tab_writer`: `ShellT.shell_runE`, `ThrData.thrDataStage2`, ShellX's dimension stage
`NumsX.numsM cr` at star parameters with `r = rowBr cr n`) and the unit machine `tabUP W`. **`tabP_writer`**:
from `frame w` on its input port (`w = reqT n M B errExp L 0 |FlatSeed|` at `n = P.n`), the writer halts with the
list seeds' flat tables `flatWord Pl L` (`tablesJ` at `L = |G_j|`) on its output port, every head back at `0`,
the request kept, residues within the budget. The size facts (the loop bound past `|FlatSeed|`, the scrub capacity
past the unit cost, the POP setup program's polynomial need `runNeed`, the table's capacities) are hypotheses here,
discharged by the bounds.

Paper quantity of the main type: the list seeds' flat tables `flatWord Pl L` (`tablesJ`, list:flatten
P3:1508-1520) on the writer's output. -/

set_option autoImplicit false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellT NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.BlockPlatform NearCubicWires.SupplierPipeline

variable (W : WalkBankProducer)

/-- **The flat tables writer.** -/
noncomputable def tabMP (cr D C DL CL : ℕ) :=
  shellMG (PrimThrW.ShellE.toV1 ThrData.thrDataStage2) W.x (tabUP W) D C 1 64 1 (cr + 18) DL CL (NumsX.numsM cr)

/-- The flat tables writer's request word. -/
def reqP (n : ℕ) (Pl : FlatListParams) (L : ℕ) : List Bool :=
  TabW.reqT n Pl.M Pl.B Pl.errExp L 0 (Fintype.card Pl.FlatSeed)

/-- **The flat tables writer's run.** -/
theorem tabP_writer (cr : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (Pl : FlatListParams)
    (L D C DL CL cap nU Bud : ℕ)
    (hb : Fintype.card Pl.FlatSeed ≤ UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hboot : ShellD.bootCost (reqP P.n Pl L) P.n 0 0 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hN : ∀ f off, f ≤ Fintype.card Pl.FlatSeed → off ≤ Fintype.card Pl.FlatSeed →
      PopSetupRun.runNeed Pl.M Pl.B Pl.errExp f 0 0 0 0 off L ≤ cap)
    (hcapC : 8 * FinalPass.Flat.sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap)
    (hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap) (hcT : tabLenP Pl L ≤ cap)
    (hc : 2 * (reqP P.n Pl L).length + 2 ≤ cap)
    (hj : UnaryCalc.value DL CL (2 ^ NumsX.mOf P) ≤ cap)
    (hnU : ∀ j < UnaryCalc.value DL CL (2 ^ NumsX.mOf P),
      cpCost (Data.unaryList [0]).length + 1 + (decBoundP (reqP P.n Pl L).length j + 1 + PopSetupRun.popCost cap + 1 +
        tabPrePCost Pl L (popRW Pl) (popRW Pl) + 1 + emitPBound cap j (tabLenP Pl L)) ≤ nU)
    (hB : 2 * shellCostG (reqP P.n Pl L) P.n D C 1 64
      (ThrData.thrDataStage2.cost 0 (TabW.noCs P.n) [] (UnaryCalc.value 1 64 P.n) (UnaryCalc.value 1 64 P.n)) 1
      (cr + 18) (TabW.c2Of cr P.n) (NumsX.mOf P) DL CL nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (tabMP W cr D C DL CL) Bud (shellInX W.x D 1 1 DL) (shellOutX W.x D 1 1 DL)
      (reqP P.n Pl L) (flatWord Pl L) := by
  have hw : reqP P.n Pl L =
      Data.reqW P.n true (ReqBridge.thrCodes (TabW.noCs P.n)) (([] : List (Stars.Carrier P.n)).map Stars.Carrier.code)
        (Data.unaryList [Pl.M, Pl.B, Pl.errExp, L, 0, Fintype.card Pl.FlatSeed]) := by
    rw [TabW.thrCodes_noCs]; rfl
  have hx2 := ShellT.dimOK_nums (x := W.x) (D := D) (D2 := 1) (Dv := 1) (DL := DL) cr P hrP _
    (reqP P.n Pl L) (TabW.reqT_eq _ _ _ _ _ _ _)
    (UnaryCalc.value 1 (cr + 18) P.n) (by simp [UnaryCalc.value]; nlinarith)
  have run := shell_runE ThrData.thrDataStage2 W.x (tabUP W) D C 1 64 1 (cr + 18) DL CL (NumsX.numsM cr)
    (TabW.c2Of cr P.n) (NumsX.mOf P) cap nU Bud (TabW.noCs P.n) ([] : List (Stars.Carrier P.n)) _ _ (tabEmitP Pl L)
    hw (TabW.dataOK_noCs P.n) hx2 hcap hR hboot (fun j hjb out => by
      rw [TabW.thrCounts_noCs]
      exact unit_okP cap W Pl P.n L j _ out _ nU rfl hN hcapC hO hcT hc (by omega) (hnU j hjb))
    hB
  rw [tabEmitP_flat Pl L _ hb] at run
  exact run

end NearCubicWires.WireExponent3_5.FinalPass.SymF
