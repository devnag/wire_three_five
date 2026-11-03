import Proof.Rows.MaskProductRowReady
import Proof.PCP.VerifierDecodingRepeatBody

/-! The right-minor loop in Cartesian monomial multiplication. Each actual
iteration emits one record and increments the unary output counter. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable abbrev inner := RepeatMachine.machine machine (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
