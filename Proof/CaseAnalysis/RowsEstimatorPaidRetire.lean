import Proof.CaseAnalysis.RowsEstimatorPaidDriverReady
import Proof.CaseAnalysis.RowsEstimatorDriverRetire

/-! Retire both actual D words at their final shared-bank locations. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def retireSlots (a : WilliamsAlgorithm) (p : Program) : Fin 2 → Fin (tapes a p) :=
  ![old a p (WarmPrepare.driver p),(ScannedClean.fresh a 1).natAdd (WarmPrepare.tapes p)]
noncomputable def retire (a : WilliamsAlgorithm) (p : Program):=RecoveryFocus.machine (retireSlots a p) DriverRetire.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
