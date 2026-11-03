import Proof.Packets.PacketsXDescendingWindowOuter

/-! Both actual nested runtime loops of the exact-order window source.
The outer physical count is width+1; metadata changes and every inner cursor
return are included in the charged finite execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowScalar

noncomputable def machine := RepeatMachine.machine DescendingWindowOuter.machine (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowLoop
