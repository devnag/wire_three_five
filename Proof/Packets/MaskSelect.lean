import Std.Tactic
import Proof.PCP.ProjectionNormalizationSuffixRestore

/-! Physical conditional decoding of one framed support record. The decision
is read from the coefficient tape; each retained row increments a real unary
counter, while a rejected row emits no mask bits. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskSelect
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

@[simp] theorem read_flag (b : Bool) : readTapeBit [b] 0 = b := rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskSelect
