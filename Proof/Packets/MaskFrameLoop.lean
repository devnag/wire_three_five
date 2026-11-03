import Proof.Packets.MaskFrame
import Proof.PCP.VerifierDecodingRepeatBody

/-! An actual counted loop framing a flat bank of raw masks. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable abbrev loop := RepeatMachine.machine machine (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
