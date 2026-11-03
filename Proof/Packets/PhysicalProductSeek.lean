import Proof.Packets.PhysicalRepeatStep
import Proof.Rows.PhysicalDriverMoves

/-! Paid forward movement by a product of two resident unary counts. No
computed product word or destination head position is supplied to the machine. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalProductSeek
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def inner := RepeatMachine.machine (Completion.PhysicalDriverMoves.machine 1 .right) (fun _ _=>true)
noncomputable def machine := RepeatMachine.machine inner (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalProductSeek
