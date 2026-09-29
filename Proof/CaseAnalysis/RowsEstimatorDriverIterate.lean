import Proof.CaseAnalysis.RowsEstimatorDriverReturnMany
import Proof.CaseAnalysis.RowsEstimatorDriverSweepRound

/-! A finite, program-constant number of actual cleanup passes. Each
composition handoff is included in the execution receipt. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverIterate
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def states (s : ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => states s n+s
def stop (t : ℕ) : Machine t 1 := ⟨0,0,fun _ => true,fun _ _ => none⟩
def machine {t s : ℕ} (p : Machine t s) : (n : ℕ) → Machine t (states s n)
  | 0 => stop t
  | n+1 => Composition.machine (machine p n) p

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.DriverIterate
