import Proof.CaseAnalysis.RowsEstimatorDriverLayout

/-! The paid scanner's actual d,p,G,C ports feed the fixed driver directly.
Every one of the original70 words is retained; no scalar copy or count pass
is inserted before the driver arithmetic. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
open LocalBitMultitape RecoveryRootRound MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def tapes (a : WilliamsAlgorithm) := 70+DriverLayout.tapes a
noncomputable def source (a : WilliamsAlgorithm) : Fin 4 → Fin (tapes a) :=
  ![(0 : Fin 70).castAdd _,(17 : Fin 70).castAdd _,(34 : Fin 70).castAdd _,(68 : Fin 70).castAdd _]
noncomputable def slots (a : WilliamsAlgorithm) : Fin (DriverLayout.tapes a) → Fin (tapes a) :=
  DriverPorts.slots 70 (source a) (by rfl)
noncomputable def machine (a : WilliamsAlgorithm) := RecoveryFocus.machine (slots a) (DriverLayout.machine a)
noncomputable def driver (a : WilliamsAlgorithm) := slots a (DriverLayout.output a)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.ScannedDriver
