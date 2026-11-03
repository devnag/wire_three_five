import Proof.Packets.ParityFilterBody

/-! An ordinary counted loop filters a resident candidate bank by coefficients
computed from the original raw polynomial. Both counts are actual unary tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding



noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
