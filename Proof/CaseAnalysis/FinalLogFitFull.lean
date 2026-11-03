import Proof.CaseAnalysis.FinalLogFit

namespace NearCubicWires.RepairSource.CloseoutFinal.C10LogFitFull

open NearCubicWires.RepairSource.CloseoutFinal.C10LogFit

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The single onset at which hypotheses 9, 10 and 11 of `S6.md` §2 all hold.
Explicitly `2 ^ (kappa * kappa + kappa) + 2`. -/
def fullOnset (kappa : ℕ) : ℕ := logFit_onset kappa + 2

theorem logFit_onset_le_fullOnset (kappa : ℕ) : logFit_onset kappa ≤ fullOnset kappa := by
  unfold fullOnset
  omega

/-- **Hypothesis 10 (`hfit`)**, at `fullOnset`.  This is `C10LogFit.hfit_of_onset`
transported up the onset; it is not re-proved. -/
theorem hfit_full (kappa : ℕ) :
    ∀ w, fullOnset kappa ≤ w → kappa * (Nat.log 2 w + 1) ≤ w := by
  intro w hw
  exact hfit_of_onset kappa w (Nat.le_trans (logFit_onset_le_fullOnset kappa) hw)


end NearCubicWires.RepairSource.CloseoutFinal.C10LogFitFull
