import W3.Recovery3.Case2Dock
import Proof.Amplification.RecoveryCaseOneBooleanOutput
import Recovery.HardTableRuns

/-!
# The Case-2 chain, part 6: the framed Case-2 bit on the recovery's port bank

The consumer (`Case2Kit.run`, gates `HTKit`) reads `frame (bit.toNat.bits)` on an output tape `≥ 5` after a run
started on gates' `Recovery.portInput` (the five words on tapes `0..4`). Proof 1's Case-2 execution `S.erun` leaves the
singleton `[bit]` on its output slot, started from `Cold.input` (the same five words on `0..4`). This file adds proof 1's
Boolean framing worker (`RecoveryCaseOneBooleanOutput`, as in base `CaseTwoSelectedOutputRun`) on two fresh tapes, over
any `SBlock`, and identifies the two entry banks (`kinput_port`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

namespace SBlock

noncomputable section


end

end SBlock

end W3.NearCubicWires.RepairSource.Outer3.Case2
