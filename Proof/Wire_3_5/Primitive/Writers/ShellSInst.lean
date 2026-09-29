import Proof.Wire_3_5.Primitive.Writers.ShellSRun
import Proof.Wire_3_5.Primitive.Writers.NumsXSRun

/-! # The SYM writer shell v2 at `m_S`

`ShellS.shell_runS` (ShellX's run at any `DimOK` dimension stage) at the SYM dimension stage `NumsXS.numsMS`
(`NumsXS.dimOK_numsS`): the SYM writer's scrub capacity `R = C(2^{m_S}+1)^D` and loop bound `b = CL(2^{m_S}+1)^DL`,
`m_S = mOfT KF P + T`, which reach the SYM tape's FILTER units (`2^{Θ(L²)}`) and POP units (`2^{Θ(√B·L)}`).

* **`shell_runSym`** (`WriterIfaceJ.WriterRun` for any decode meeting `CellUnit.DecOK` at every unit `j < b`).

Paper quantity of the main type: the SYM writer's output tape `(List.range b).flatMap emit ++ [false]` (C4's `BAT` word
of the call, `SymDec.sym_loop_tape`) at the dimension `2^{m_S}` (prim:runtime P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellS
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline

/-- **The SYM writer shell v2's run at `m_S`.** -/
theorem shell_runSym (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (D C D2 C2 Dv Cv DL CL KF cr : ℕ) {ζ : ℚ}
    (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (Cc : Ledger.CapParams) (D2' K0 cap nU Bud : ℕ) {n a' : ℕ}
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (tl w : List Bool)
    (emit : ℕ → List Bool) (P : Shared.StarParams) (hPn : P.n = n) (hrP : P.r = Ledger.rowBr cr P.n)
    (hw : w = Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : DataOK Cs carriers (UnaryCalc.value D2 C2 n))
    (hN : NumsXS.SNeed (UnaryCalc.value Dv Cv n) P h0 h1 Cδ Cc D2' K0 KF cr)
    (hcap : cap + 1 ≤ UnaryCalc.value D C (2 ^ NumsXS.mS KF P h0 h1 Cδ Cc D2' K0))
    (hR : nU + 1 ≤ UnaryCalc.value D C (2 ^ NumsXS.mS KF P h0 h1 Cδ Cc D2' K0))
    (hboot : bootCost w n 0 0 ≤ UnaryCalc.value D C (2 ^ NumsXS.mS KF P h0 h1 Cδ Cc D2' K0))
    (hdec : ∀ j < UnaryCalc.value DL CL (2 ^ NumsXS.mS KF P h0 h1 Cδ Cc D2' K0), ∀ out : List Bool, ∃ σD m Bp,
      WExec cap decW (blankCellD W.x w out j (Data.unaryList (Data.symCounts a' Cs carriers))) σD m ∧
      DecOK cap W σD out (emit j) Bp ∧ σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧
      σD.sh (sk W.x 2) = 0 ∧
      cpCost (Data.unaryList (Data.symCounts a' Cs carriers)).length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU)
    (hB : 2 * ShellT.shellCostG w n D C D2 C2
      (Data.coreCost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv
      (2 * NumsXS.numsStageCostS (UnaryCalc.value Dv Cv n) P h0 h1 Cδ Cc D2' K0 KF cr + 2)
      (NumsXS.mS KF P h0 h1 Cδ Cc D2' K0) DL CL nU + 2 ≤ Bud) :
    WriterIfaceJ.WriterRun (shellMS W decW D C D2 C2 Dv Cv DL CL (NumsXS.numsMS KF cr ζ Cδ Cc D2' K0)) Bud
      (shellInX W.x D D2 Dv DL) (shellOutX W.x D D2 Dv DL) w
      ((List.range (UnaryCalc.value DL CL (2 ^ NumsXS.mS KF P h0 h1 Cδ Cc D2' K0))).flatMap emit ++ [false]) := by
  subst hPn
  exact shell_runS W decW D C D2 C2 Dv Cv DL CL (NumsXS.numsMS KF cr ζ Cδ Cc D2' K0)
    (2 * NumsXS.numsStageCostS (UnaryCalc.value Dv Cv P.n) P h0 h1 Cδ Cc D2' K0 KF cr + 2)
    (NumsXS.mS KF P h0 h1 Cδ Cc D2' K0) cap nU Bud Cs carriers tl w emit hw hD
    (NumsXS.dimOK_numsS KF cr P hrP h0 h1 Cδ Cc D2' K0 _ w (hw.trans (reqW_natWord _ _ _ _ _)) _ hN)
    hcap hR hboot hdec hB

end NearCubicWires.WireExponent3_5.PrimAsm.ShellS
