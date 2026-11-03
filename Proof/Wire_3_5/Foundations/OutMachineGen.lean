import Lean
import Proof.Wire_3_5.Foundations.OutMachineP5
import Proof.Wire_3_5.Primitive.SeedFix.C4KWd
import Proof.Wire_3_5.MachineModel.BlockJoin
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.Foundations.OutMachineIface
import Proof.Wire_3_5.Foundations.OutMachineGenBase


noncomputable section
set_option maxRecDepth 4096


/-! # X6: the out machine (`Bank.OutGen mOut`)

"At one sampled input, [...] This takes polynomial time without evaluating a monomial expansion" (P3:3175-3178); the
final pass prints its estimate `ratWord (Num/Den)` (P3:3044-3048). The six phases (`Out.Iface`) compose by
`WExec.seq` into ONE word program `outP`; base's masked reset (`C4KW.wm_blankR`) turns its run from blank registers
into a machine run with every head back at `0` (cost `2n + 2`); `Block.dockKeep` docks it by `slotsO` (`O, N, D` on
`o, tN, tD`, the other 21 tapes on the room `e`).

* **`outP_run`**: from the entry (`Num`, `Den` on `N`, `D`), the phases' values chain (`strip_spec`, `oddPart_spec`,
  `gcd_oddPart`, `reduce_eq`) to `O = ratWord (Num/Den)`, every register `0`;
* `roomIdx`, **`slotsO`**, `slotsO_inj`, `entryOf` (the word state read off the bank), `tin_eq`;
* **`outOfPhases : OutOfPhases`**; **`outGen : Bank.OutGen mOut`** (the six proved phases);
  **`outGen_D`** (`= Dout = 2`), **`outGen_C`** (`= Cout = 6620`), plain constants for every layout.

Paper quantity of the main type: the printed rational `ratWord (Num/Den)` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Gen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Out
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot)

/-! ## The word program -/

/-! ## The dock -/

/-! ## The out machine -/

/-- **X6's assembly**: the six phases give the out machine's target. -/
noncomputable def outOfPhases : OutOfPhases := fun p1 p2 p3 p4 p5 p6 _t o tN tD sc e hsc he hoN hoD hND =>
  { s := (outP p1 p2 p3 p4 p5 p6).toProg.size + 2
    M := machO o tN tD e p1 p2 p3 p4 p5 p6
    cost := fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2
    C := 2 * (p1.C + p2.C + p3.C + p4.C + p5.C + p6.C) + 12
    D := 2
    cost_le := cost_bound p1 p2 p3 p4 p5 p6
    exitA := exitO (machO o tN tD e p1 p2 p3 p4 p5 p6) (fun W => 2 * nTot p1 p2 p3 p4 p5 p6 W + 2)
    run := fun Ab W num den hN hD hO hbl hn hd hd0 =>
      outOf_run p1 p2 p3 p4 p5 p6 o tN tD sc e hsc he hoN hoD hND Ab W num den hN hD hO hbl hn hd hd0 }

end NearCubicWires.WireExponent3_5.FinalPass.Out.Gen

end
