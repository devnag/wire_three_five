import Proof.Supplier.EquationScalarWiden

/-! The paid driver-controlled widening loop for one weight block. Source
and output cursors remain streaming; only the actual count driver rewinds. -/
namespace NearCubicWires.RepairOrdinary.EquationWidenLoop
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


noncomputable def machine := RepeatMachine.machine EquationWiden.machine (fun _ _ => true)

end NearCubicWires.RepairOrdinary.EquationWidenLoop
