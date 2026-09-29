import Proof.Amplification.RecoveryPCPFormulaResumeRandom
import Proof.MachineModel.Runs
import Proof.Supplier.RowCommonResources

/-! Compute the actual native pool cardinality from the exponential driver
already produced by BinaryInitialize and the decoded ORIGINAL child count.
No replicated-count word is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdPoolCount
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding
open RowCommonSize (put focus_put)



end NearCubicWires.P1Closure.BinaryCacheColdPoolCount
