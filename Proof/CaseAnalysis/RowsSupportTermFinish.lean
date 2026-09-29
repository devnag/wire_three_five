import Proof.CaseAnalysis.RowsCircuitTermSupplier
import Proof.CaseAnalysis.RowsSupportTermLayout
import Proof.CaseAnalysis.RowsSupportThresholdCircuit

/-! A successful literal term commits its original coefficient and clears
exactly the private circuit bank. This is the actual last two calls of the
fixed term controller; the failed exit never uses this clearing receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey CompetitorSumFold
open CloseoutWitness
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.Term
