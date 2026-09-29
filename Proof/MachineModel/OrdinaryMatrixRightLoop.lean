import Proof.MachineModel.OrdinaryMatrixRightBucket

/-! The whole right-bucket traversal executes the repeatable bucket body
from the physical count driver, preserves aggregate output, and pays the
final driver rewind. Width guards apply to all visited boundary values. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightLoop
open LocalBitMultitape RecoveryExecution
open MatrixRightAdvance (Store)
open MatrixRightBucket (Params width fuel cfg)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cost (p : Params) := 2*fuel p+24*width p+4*p.I+33
noncomputable def machine := RepeatMachine.machine MatrixRightBucket.machine (fun _ _ => true)
def output (p : Params) : ℕ → ℕ → ℕ → List Bool
  | _,_,0 => []
  | a,inner,n+1 => MatrixRightBucket.output p a inner++output p (a+p.B) (inner+1) n

end NearCubicWires.RepairOrdinary.MatrixRightLoop
