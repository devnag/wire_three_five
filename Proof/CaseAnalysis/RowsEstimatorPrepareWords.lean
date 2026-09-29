import Proof.CaseAnalysis.RowsEstimatorPrepareLayout

/-! Exact projection and extensionality at the owned preparation boundary. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def spare (p : Program) : Fin (tapes p) := (Reuse.output p).castAdd 7



end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepare
