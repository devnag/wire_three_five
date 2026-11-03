import Proof.CaseAnalysis.RowsEstimatorAppendCopy
import Proof.Amplification.RecoveryTseitinReadOnly

/-! The actual cold estimator retains its original native-bank capacity.
This is the same physical word subsequently used by the scratch sweep. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Retained
open LocalBitMultitape RepairRepresentation RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (p : Program) : Fin (WholePrefix.tapes p):=(68 : Fin 70).castAdd (CloseoutRowsRawRecord.tapes p)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Retained
