import Proof.Wire_3_5.FinalPass.TabFlat
import Proof.Wire_3_5.Primitive.Writers.ShellERun
import Proof.Wire_3_5.Primitive.Writers.ThrData2

/-! # S4 (f1), the tables writer, part 9: the writer run (the ShellE shell, P3:2036-2101)

The tables writer is the THR writer shell over the data stage v2 (`ShellT.shell_runE`, the empty THR tuple and no
carriers, `ThrData.thrDataStage2`), with ShellX's dimension stage `NumsX.numsM cr` (`ShellT.dimOK_nums`, at star
parameters with `r = rowBr cr n`) and the unit machine `tabU W F5`. **`tab_writer`**: from `frame w` on its input port
(`w` the unit request word `reqT n len cap err L₀ L₁ |seeds|` at `n = P.n`), the writer halts with the seeds' tables
`tabWord FP L₀ L₁ ++ [false]` on its output port, every head back at `0`, the request kept, residues within the budget.
The size facts (the loop bound past `2·|seeds|`, the scrub capacity past the unit cost and the cell capacity, the
unit's capacity needs) are hypotheses here, discharged by the bounds.

Paper quantity of the main type: the seeds' filter tables (`tabWord`, P3:2036-2101) on the writer's output. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellT NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.BlockPlatform NearCubicWires.SupplierPipeline

/-- The empty THR tuple. -/
def noCs (n : ℕ) : Fin 0 → NormalizedThresholdThresholdCircuit n := Fin.elim0

theorem thrCodes_noCs (n : ℕ) : ReqBridge.thrCodes (noCs n) = [] := by simp [ReqBridge.thrCodes]

theorem thrCounts_noCs (n : ℕ) : ThrData.thrCounts (noCs n) [] = [0] := by
  simp [ThrData.thrCounts, PrimT.ThrTab.tupleG]

theorem dataOK_noCs (n : ℕ) : PrimThrW.ShellE.ThrDataOK2 (noCs n) [] (UnaryCalc.value 1 64 n) := by
  have hb : natBitLength n ≤ n + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have hv : UnaryCalc.value 1 64 n = 64 * (n + 1) := by simp [UnaryCalc.value]
  have h0 : natBitLength 0 = 1 := by simp [natBitLength]
  refine ⟨by omega, by simp, fun i => i.elim0, fun X hX => by simp at hX, by rw [hv]; omega, by rw [hv]; omega,
    ?_, ?_, fun y hy => by simp [thrCodes_noCs] at hy, fun y hy => by simp at hy, ?_⟩
  · rw [h0, hv]; norm_num; omega
  · simp only [List.length_nil]; rw [h0, hv]; norm_num; omega
  · rw [thrCounts_noCs, hv]; simp [Data.unaryList]; omega

variable (W : WalkBankProducer) (F5 : FiltSetupSpec5 W)

/-- The dimension stage's cost at the request. -/
def c2Of (cr n : ℕ) : ℕ := 2 * NumsX.numsStageCost n cr (UnaryCalc.value 1 (cr + 18) n) + 2

/-- **The tables writer.** -/
noncomputable def tabM (cr D C DL CL : ℕ) :=
  shellMG (PrimThrW.ShellE.toV1 ThrData.thrDataStage2) W.x (tabU W F5) D C 1 64 1 (cr + 18) DL CL (NumsX.numsM cr)

/-- **The tables writer's run.** -/
theorem tab_writer (cr : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (FP : GapParams) (L0 L1 D C DL CL cap
    nU Bud : ℕ)
    (hb : 2 * Fintype.card (GapSeed FP) ≤ UnaryCalc.value DL CL (2 ^ NumsX.mOf P))
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hboot : ShellD.bootCost (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) P.n 0 0 ≤
      UnaryCalc.value D C (2 ^ NumsX.mOf P))
    (hU1 : 1 ≤ FP.cap)
    (hneed : ∀ L, L = L0 ∨ L = L1 → F5.need FP.len FP.cap FP.errExp L 0 0 0 (Fintype.card (GapSeed FP)) ≤ cap)
    (htab : ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 → (tableWord (filterTable FP e L)).length ≤ cap)
    (hc : 2 * (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length + 2 ≤ cap)
    (hj : UnaryCalc.value DL CL (2 ^ NumsX.mOf P) ≤ cap) (hc2 : 2 ≤ cap)
    (hnU : ∀ j < UnaryCalc.value DL CL (2 ^ NumsX.mOf P), ∀ (e : GapSeed FP) (L : ℕ), L = L0 ∨ L = L1 →
      cpCost (Data.unaryList [0]).length + 1 +
        (decBound (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length j + 1 + F5.bound cap +
          1 + tabPreCost FP L (rulerW FP) (rulerW FP) + 1 +
          emitBound (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))).length j
            (tableWord (filterTable FP e L)).length) ≤ nU)
    (hB : 2 * shellCostG (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) P.n D C 1 64
      (ThrData.thrDataStage2.cost 0 (noCs P.n) [] (UnaryCalc.value 1 64 P.n) (UnaryCalc.value 1 64 P.n)) 1 (cr + 18)
      (c2Of cr P.n) (NumsX.mOf P) DL CL nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (tabM W F5 cr D C DL CL) Bud (shellInX W.x D 1 1 DL) (shellOutX W.x D 1 1 DL)
      (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) (tabWord FP L0 L1 ++ [false]) := by
  have hw : reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP)) =
      Data.reqW P.n true (ReqBridge.thrCodes (noCs P.n)) (([] : List (Stars.Carrier P.n)).map Stars.Carrier.code)
        (Data.unaryList [FP.len, FP.cap, FP.errExp, L0, L1, Fintype.card (GapSeed FP)]) := by
    rw [thrCodes_noCs]; rfl
  have hx2 := ShellT.dimOK_nums (x := W.x) (D := D) (D2 := 1) (Dv := 1) (DL := DL) cr P hrP _
    (reqT P.n FP.len FP.cap FP.errExp L0 L1 (Fintype.card (GapSeed FP))) (reqT_eq _ _ _ _ _ _ _)
    (UnaryCalc.value 1 (cr + 18) P.n) (by simp [UnaryCalc.value]; nlinarith)
  have run := shell_runE ThrData.thrDataStage2 W.x (tabU W F5) D C 1 64 1 (cr + 18) DL CL (NumsX.numsM cr)
    (c2Of cr P.n) (NumsX.mOf P) cap nU Bud (noCs P.n) ([] : List (Stars.Carrier P.n)) _ _ (tabEmit FP L0 L1) hw (dataOK_noCs P.n) hx2 hcap hR
    hboot (fun j hjb out => by
      rw [thrCounts_noCs]
      exact unit_ok cap W F5 FP P.n L0 L1 j _ out _ nU rfl hU1 hneed htab hc (by omega) hc2
        (fun e L hL => hnU j hjb e L hL))
    hB
  rw [tabEmit_flat FP L0 L1 _ hb] at run
  exact run

end NearCubicWires.WireExponent3_5.FinalPass.TabW
