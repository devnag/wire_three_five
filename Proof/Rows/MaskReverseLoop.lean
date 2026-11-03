import Proof.Rows.MaskReverse

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := RepeatMachine.machine body (fun _ _ => true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
