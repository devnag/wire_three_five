import Proof.CaseAnalysis.RowsEstimatorDriverSupport

/-! One actual offset D sweep, followed by return of only its D cursor.
A second retained D word and the D+1 log are reused between fixed passes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def returnSlots (t : ℕ) : Fin 3 → Fin (t+1+2) :=
  ![(((0 : Fin 1).natAdd t).castAdd 2),((0 : Fin 2).natAdd (t+1)),((1 : Fin 2).natAdd (t+1))]

def roundFirst (t : ℕ) := TapeEmbedding.machine 2 (RecoveryScratchErase.machine t)
noncomputable def roundLast (t : ℕ) := RecoveryFocus.machine (returnSlots t) CompetitorRecordRewind.machine
noncomputable def round (t : ℕ) := Composition.machine (roundFirst t) (roundLast t)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverSweep
