import Lean
import Proof.Wire_3_5.Primitive.Writers.SymNums
import Proof.Wire_3_5.Primitive.Writers.SymLeafIface
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (SYM leaf), part 8: the SYM writer's run at one call, with the budgets as hypotheses

The SYM writer is the SYM shell v2 (`ShellS.shell_runSym`, the dimension `m_S` at `D₂' = 26`, `K₀ = 6`) with PA's SYM
unit decode `SymDec.decW` (the FILTER bank and the POP bank `pbW Q`). **`sym_ready`**: at a SYM call of the gate's
family, from the numeric budget hypotheses (the decode's needs `sym_hdec_pop`, the data width, the fill `SNeed`, the
scrub, the loop's length `b ≥ TOT`, the unit budget `nU ≥ symNU …`), the writer's run within `Bud` prints the call's
SYM tape `symTape` (`sym_loop_tape`).

Paper quantity of the main type: the SYM tape `symTape` (C4's `BAT` word of the call, P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellState
open NearCubicWires.WireExponent3_5.PrimAsm.CellUnit NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.Records
open NearCubicWires.WireExponent3_5.PrimAsm.Emit NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.SymDecEnum
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe
open NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

section Ready
variable (cap : ℕ) (W : WalkBankProducer)

/-- **The SYM writer's run at one call of the gate's family**, the budgets as hypotheses. -/
theorem sym_ready (FS : FiltSetupSpec5 W) (Q : PopSetupSpec W) (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ)
    (ha0 : a0 ≤ kclk + 1) (D C D2 C2 Dv Cv DL CL KF nU Bud : ℕ) {n : ℕ}
    (hs : (Plan.callInputs l F kclk coef A a0 ha0).StarAt n) {a : ℕ}
    (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (tl w : List Bool)
    (Kb Cmax Bb BP : ℕ) (ha : a ≤ 4) (hnc : carriers.length ≤ 2)
    (hw : w = Data.reqW n false (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) tl)
    (hKb : ∀ c ∈ Data.symCodes a Cs, natBitLength c ≤ Kb)
    (hC : ∀ c ∈ carriers.map (·.length) ++ cyOf Cs, c ≤ Cmax)
    (hN1 : P1Need cap w n (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (cyOf Cs)
      Kb Cmax)
    (hcS : (F.filterErrDeg + 4) * (n + 3) + 2 * F.cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n) (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1) ≤ cap)
    (hcC : CapNeed (gateCap l) .sym n ((Ledger.rowBr F.cr n)) (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) cap)
    (hN2 : NumsNeed cap n ((((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (F.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length
      (Ledger.Lq n) (SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0)
      ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0))
    (hI : UnaryCalc.value DL CL (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6) + totV n ((((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (F.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n)
      (SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) a ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0)
      ((cyOf Cs).getD 3 0) + euV (cyOf Cs).sum carriers.length a + 2 * (cyOf Cs).sum +
      2 ^ (2 * SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) +
      stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) +
      2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length ((((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n))) (Ledger.Lq n + 5) + carriers.length + 20 ≤ cap)
    (hU : 1 ≤ (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n))
    (hcF : 4 * 2 ^ (2 * SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum ≤ cap)
    (hFc : fbCost cap + FS.bound cap ≤ Bb)
    (hFN : ∀ (eg : GapSeed ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n)) (r row : ℕ), r < carriers.length →
      row < 2 ^ (2 * SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) →
      FS.need ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n).len ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n).cap ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n).errExp
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) (2 * (2 * row))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0)) (Fintype.card (GapSeed ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n))) ≤ cap ∧
      filtPipeBound ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n) eg
          (fbL r ((carriers.map (·.length)).getD 0 0) ((carriers.map (·.length)).getD 1 0)) (2 * (2 * row))
          (2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + (cyOf Cs).sum)
          (fbOff r ((carriers.map (·.length)).getD 0 0)) (rulerW ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n))
          (rulerW ((Plan.callInputs l F kclk coef A a0 ha0).filterParams .sym n)) ≤ BP)
    (hQc : pbCost cap + Q.bound cap ≤ Bb)
    (hcB : stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) +
      7 * (cyOf Cs).sum + bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) + Ledger.Lq n +
      2 ^ FlatNums.fbv (cyOf Cs).sum (bV carriers.length (((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n)) (Ledger.Lq n + 5) +
      4 * 2 ^ (2 * SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) +
      2 * ((carriers.map (·.length)).getD 0 0 + (carriers.map (·.length)).getD 1 0) + 40 ≤ cap)
    (hPN : ∀ i : ℕ, i < a → ∀ (e' : (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers).FlatSeed) (row : ℕ) (sgn : Bool)
      (s : Fin ((symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers).M + 1)), row < 2 ^ (2 * SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) →
      Q.need (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers) (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) ≤ cap ∧
      ∀ hl : 4 * pbdL Cs i ≤ (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)).length,
        popPipeBound cap (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers) e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers)
          (pbdOff Cs carriers i) (popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popLw (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers) (pbdL Cs i))
          (popR (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popCp (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popRW (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers)) (popRW (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers)) sgn s hl ≤ BP)
    (hD : ShellD.DataOK Cs carriers (UnaryCalc.value D2 C2 n))
    (hN : NumsXS.SNeed (UnaryCalc.value Dv Cv n) ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 KF F.cr)
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6)) (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6)) (hboot : ShellD.bootCost w n 0 0 ≤ UnaryCalc.value D C (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6))
    (hTOT : symNT (Plan.callInputs l F kclk coef A a0 ha0) hs Cs carriers * (2 ^ SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) ^ 2 *
      ((carriers.length + 2 * a) * ((symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers).M + 3) + 2) ≤ UnaryCalc.value DL CL (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6))
    (hnU : symNU (Data.unaryList (Data.symCounts a Cs carriers)).length
          (4 * UnaryPow.sq cap + 1 + (reqParseCost n a carriers.length Kb + 1 + (5 * UnaryPow.sq cap + 1 +
        (30 * UnaryPow.sq cap + 1 + countsCost carriers.length Cmax (cyOf Cs).sum))) + 1 +
        (starCapCost n F.cr (Plan.callInputs l F kclk coef A a0 ha0).filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
          (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) cap +
        1 + (500 * UnaryPow.sq cap + 1 + (30 * UnaryPow.sq cap + 1 + 26 * UnaryPow.sq cap))) + 1 + (Bb + 12)) BP (UnaryCalc.value DL CL (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6)) ≤ nU)
    (hB : 2 * ShellT.shellCostG w n D C D2 C2
      (Data.coreCost a Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv
      (2 * NumsXS.numsStageCostS (UnaryCalc.value Dv Cv n) ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6
        KF F.cr + 2) (NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6) DL CL nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (ShellS.shellMS W (decW W FS (pbW W Q) F.cr (Plan.callInputs l F kclk coef A a0 ha0).filterErrDeg (gateCParams1 l).ζ (gateCδ1 l)
        (gateCap l)) D C D2 C2 Dv Cv DL CL (NumsXS.numsMS KF F.cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) 26 6)) Bud
      (ShellX.shellInX W.x D D2 Dv DL) (ShellX.shellOutX W.x D D2 Dv DL) w (WriterIface.symTape (Plan.callInputs l F kclk coef A a0 ha0) hs Cs carriers) := by
  have hdec : ∀ j < UnaryCalc.value DL CL (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6), ∀ out : List Bool, ∃ σD m Bp,
      WExec cap (decW W FS (pbW W Q) F.cr (Plan.callInputs l F kclk coef A a0 ha0).filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l))
        (CellLoopD.blankCellD W.x w out j (Data.unaryList (Data.symCounts a Cs carriers))) σD m ∧
      DecOK cap W σD out ((unitE (symNT (Plan.callInputs l F kclk coef A a0 ha0) hs Cs carriers * (2 ^ SeedFix.callKh ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs)) ^ 2 *
        ((carriers.length + 2 * a) * ((symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers).M + 3) + 2)) (carriers.length + 2 * a)
        (symListParams (Plan.callInputs l F kclk coef A a0 ha0) n a Cs carriers).M (SymFlat.symCallUnit (Plan.callInputs l F kclk coef A a0 ha0) hs Cs carriers)) j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      CellLoopD.cpCost (Data.unaryList (Data.symCounts a Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU := by
    intro j hj out
    obtain ⟨σD, m, Bp, e, d, k0, k2, k2h, hm⟩ := sym_hdec_pop cap W FS Q F.cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l)
      (gateCap l) (Plan.callInputs l F kclk coef A a0 ha0) hs Cs carriers tl w (UnaryCalc.value DL CL (2 ^ NumsXS.mS KF ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6)) Kb Cmax Bb BP ha hnc rfl rfl rfl rfl hw hKb hC hN1 hcS hcP hcC hN2 hI hU
      hcF hFc hFN hQc hcB hPN j hj out
    exact ⟨σD, m, Bp, e, d, k0, k2, k2h, le_trans hm hnU⟩
  have hrun := ShellS.shell_runSym W (decW W FS (pbW W Q) F.cr (Plan.callInputs l F kclk coef A a0 ha0).filterErrDeg (gateCParams1 l).ζ (gateCδ1 l) (gateCap l))
    D C D2 C2 Dv Cv DL CL KF F.cr (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 cap nU Bud Cs carriers tl w
    _ ((Plan.callInputs l F kclk coef A a0 ha0).starParams n hs) rfl rfl hw hD hN hcap hR hboot hdec hB
  rw [sym_loop_tape (Plan.callInputs l F kclk coef A a0 ha0) hs Cs carriers _ hTOT] at hrun
  exact hrun

end Ready

end NearCubicWires.WireExponent3_5.PrimAsm.SymDec

end
