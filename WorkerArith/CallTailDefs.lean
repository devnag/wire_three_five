import WorkerArith.CtrCall
import WorkerArith.VerdictVal
import Codec.PairFrame

/-!
# W3dl: the call tail (programs + statements `clearFrame_ideal`, `callTail_ideal`)

The near-cubic-gates paper: a nonexact term is one counter call on the call word and the term's witness prefix; its
entry is `(flip, ctr.value c w)`. The call tail: frame the witness field `w` (`Codec.fieldFrameW`, onto `S2`),
build the counter's input `frame (frame (callWord c) ++ frame w)` on its input tape (`Codec.pairFrame`), append the
flip bit to the I-stream `VI`, run the clocked counter (`ctrCallP`, which appends `marks (outputWord …)` and clears
every counter tape), and blank `S1`, `S2` (`clearFrameP`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Joins (Counter Call callWord outputWord bitWord)

/-! ## Blanking a framed word -/

/-! ## The call tail -/

end NearCubicGates.Close.WorkerArith
