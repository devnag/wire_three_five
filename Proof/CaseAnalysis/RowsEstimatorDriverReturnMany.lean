import Proof.CaseAnalysis.RowsEstimatorDriverPartialReset

/-! Return every scratch cursor in parallel by D+1 using the retained D.
The worker is the existing zero-tape scratch sweep (a driver scan), focused
into the old bank and wrapped by the existing masked recorded reset. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverReturnMany
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot (t : ℕ) : Fin 1 → Fin (t+2) := fun _ => (0 : Fin 2).natAdd t
noncomputable def body (t : ℕ) := RecoveryFocus.machine (slot t) (RecoveryScratchErase.machine 0)
noncomputable def machine (t : ℕ) := MaskedReset.machine (body t) (fun _ => true)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverReturnMany
