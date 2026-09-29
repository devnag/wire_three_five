import Proof.Wire_3_5.FinalPass.Core11

/-! # S5Core, part 12: the THR half's exit and the count and mode stages on it (P3:3083-3086, 3170-3181)

* **`exit_facts`**: at the THR half's exit (`ThrExit2`) the input is on tape `0`, the core's room is blank, the
  non-THR word slots and the number tapes are blank;
* **`stage12`**: the count then the mode from that exit: the reference `Tc = sent c` (`c = L.Kc·N^{L.Dc}`), the mode
  tape `[thrFlag mode]`, the room invariant at `10`, every tape off the room kept.

Paper quantities: the front's exact register length (`FrontOut.blank`) and the request's mode (P3:3083-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)

section Run

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core
