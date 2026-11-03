import Proof.Rows.MaskProductBody

/-! Actual left-major traversal of the Cartesian support product. Every
right-minor pass restores its right cursor before the next left row. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def outer := RepeatMachine.machine body (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
