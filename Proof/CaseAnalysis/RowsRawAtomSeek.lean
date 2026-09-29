import Proof.CaseAnalysis.RowsProjectionReset
import Proof.CaseAnalysis.RowsRawAtomLoop
import Proof.MachineModel.Semantics

/-! A raw variable block drives selection in the already-produced atom
cache. The actual prefix polynomials are scanned once, with no numeric
index conversion, count prepass, or discarded output. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomSeek
