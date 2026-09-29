import Proof.Wire_3_5.Primitive.Writers.ShellXRun
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface

/-! # THR, join (4): the THR writer shell's run TYPE (ShellX's boot over `ThrDataStage`, any unit machine)

P3:3068-3084 (lem:primitive): a THR call reads its circuits, its carriers and its translation; P3:1188-1189 and
P3:3823-3824: the call's tape has `2^(2·kh)·poly(n)` units, so the loop is dimensioned by `n' = 2^(2·kh + L)` (the ShellX). Two writers read a THR request: the THR batch writer (`WriterIfaceJ.ThrWriterAtJ`, request word
`(thrReq …).word ++ frame hashBits`) and the HASH writer (`WriterIfaceJ.HashWriterAtJ`, request word `(thrReq …).word`).
Both are `Data.reqW n true (thrCodes Cs) (carrier codes) tl` (`ReqBridge.reqW_thrReq`).

ShellX (`ShellX.shell_runX`) is SYM-typed twice over: its boot runs `Data.dataM` (the SYM data stage) and its loop body
is PA's `CellUnit.unitM`, whose branches are POP and FILTER only (`CellUnit.DecOK`). The THR batch writer prints RADIX
rows, so its unit machine is not `unitM`. This file fixes the THR shell:

* **`ThrDataOK`**: `ThrData.ThrDataStage.run`'s size hypotheses at the width `V` (`L = W = V`);
* the machines: `M8T` (the THR data stage docked on `ShellD.dataSlots`), `preMT`, `MX0T`, `bootXMT` (ShellX's boot with
  `M8T` in place of `ShellD.M8`), `bodyU` (copy-in ; ANY unit machine `U` on the cell layout), `loopEU`, `innerMT`,
  **`shellMT`**, `shellStageT`;
* **`UnitOK`**: the per-unit hypothesis on `U` (from the unit's entry `blankCellD x w out j u` to a cell state with the
  request kept, `out ++ emit j ++ [false]` on the output (head on the closing `false`), the counter `1^(j+1)`, within
  the unit budget);
* **`ThrShellRun`**: the THR shell's run TYPE (`WriterIfaceJ.WriterRun` from `frame w`, `w` the THR request word, to
  `(List.range b).flatMap emit ++ [false]`, `b = CL(2^(mOf P)+1)^DL`);
* **`unitOK_of_dec`**: PA's `unitM W decW` meets `UnitOK` wherever its decode meets `DecOK` (the HASH writer's dock).

Paper quantities of the main type: the THR request word (the call of lem:primitive), the call's slice lengths
`ThrData.thrCounts` on the data tape, and the writer's output tape `(List.range b).flatMap emit ++ [false]`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.Shell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm

/-! ## The machines -/

/-- The THR data stage, docked where `ShellD.M8` docks `Data.dataM`. -/
noncomputable def M8T (S : ThrData.ThrDataStage) (x D D1 D2 : ℕ) :=
  RecoveryFocus.machine (dataSlots x D D1 D2) S.M

/-- The boot and the THR data phase (`ShellD.preM` with `M8T`). -/
noncomputable def preMT (S : ThrData.ThrDataStage) (x D D1 D2 C1 C2 : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (bootM x D D1 D2 C1) (M6 x D D1 D2 C2))
    (M7 x D D1 D2)) (M8T S x D D1 D2)

/-- The THR pre-phase, docked on ShellX's layout (`ShellX.MX0` with `preMT`). -/
noncomputable def MX0T (S : ThrData.ThrDataStage) (x D D2 Dv DL C2 : ℕ) :=
  RecoveryFocus.machine (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) (preMT S x D 0 D2 0 C2)

/-- **The loop body for any unit machine** `U` on the cell layout: the copy-in, then `U` (`CellLoopD.bodyD` with `U`
in place of `unitM W decW`). -/
noncomputable def bodyU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (e : ℕ) :=
  Composition.machine (cpM x e) (TapeEmbedding.machine e (TapeEmbedding.machine 1 U))

/-- The unit loop with the data tape on ShellX's layout (`ShellX.loopEX` with `bodyU`). -/
noncomputable def loopEU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (D D2 Dv DL : ℕ) :=
  TapeEmbedding.machine (EX x D D2 Dv DL) (TapeEmbedding.machine (E1 0 + E2 D2 + E3)
    (CloseoutRowsDegreeLoop.machine (Scrub.machine (bodyU x U (Scrub.wk D)) (scrResetD x (Scrub.wk D))
      (scrSD x (Scrub.wk D)))))

/-! ## The per-unit hypothesis and the run type -/

/-- **One unit of the loop** (`cap` the cell encoding's capacity, `u` the data tape's counts): from the unit's entry
`blankCellD x w out j u` (request `frame w` on stream `0`, head `0`; `out ++ [false]` on stream `1`, head `|out|`;
`1^j` on stream `2`, head `0`; `u` on stream `113`, head `0`; every other stream empty, every register `0`), the unit
machine `U` halts at a cell state with the request kept on stream `0`, `out ++ emit j ++ [false]` on stream `1` with
its head at `|out ++ emit j|`, and `1^(j+1)` on stream `2`, in `mU` steps with `cpCost |u| + 1 + mU ≤ nU`. -/
def UnitOK (cap x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) (nU : ℕ) (w u : List Bool) (emit : ℕ → List Bool) (j : ℕ)
    (out : List Bool) : Prop :=
  ∃ (σE : WState (LNS x) LNR) (mU : ℕ),
    Step U mU (wenc cap (blankCellD x w out j u)).H (wenc cap (blankCellD x w out j u)).A (wenc cap σE).H
      (wenc cap σE).A ∧
    σE.st (sk x 0) = frame w ∧ σE.st (sk x 1) = out ++ emit j ++ [false] ∧ σE.sh (sk x 1) = (out ++ emit j).length ∧
    σE.st (sk x 2) = List.replicate (j + 1) true ∧ cpCost u.length + 1 + mU ≤ nU

/-! ## PA's unit machine docks by `DecOK` -/

/-- **PA's `unitM W decW` meets `UnitOK`** wherever its decode meets `DecOK` (ShellX's `hdec` shape): the HASH writer's
FILTER-only units dock the THR shell unchanged. -/
theorem unitOK_of_dec (cap : ℕ) (W : WalkBankProducer) (decW : WM (LNS W.x) LNR) (nU : ℕ) (w u : List Bool)
    (emit : ℕ → List Bool) (j : ℕ) (out : List Bool)
    (h : ∃ σD m Bp, WExec cap decW (blankCellD W.x w out j u) σD m ∧ DecOK cap W σD out (emit j) Bp ∧
      σD.st (sk W.x 0) = frame w ∧ σD.st (sk W.x 2) = List.replicate j true ∧ σD.sh (sk W.x 2) = 0 ∧
      cpCost u.length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU) :
    UnitOK cap W.x (unitM W decW) nU w u emit j out := by
  obtain ⟨σD, m, Bp, hd, hok, hIN, hC, hCh, hn⟩ := h
  obtain ⟨σE, sU, e0, e1, e1h, e2⟩ :=
    unit_step cap W decW (blankCellD W.x w out j u) σD m j Bp out (emit j) w hd hok hIN hC hCh
  exact ⟨σE, _, sU, e0, e1, e1h, e2, hn⟩

end NearCubicWires.WireExponent3_5.PrimThrW.Shell
