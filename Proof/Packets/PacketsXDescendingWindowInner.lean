import Proof.Packets.PacketsXDescendingWindowBody
import Proof.Packets.PhysicalRepeatStep

/-! Executed descending antidiagonal loop, including its actual unary loop
driver and exact native output append order. No body call is required at the
terminal counter value. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowLayout CloseoutRowsModeWindowScalar


noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
