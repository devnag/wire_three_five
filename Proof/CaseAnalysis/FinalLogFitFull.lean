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


end NearCubicWires.RepairSource.CloseoutFinal.C10LogFitFull
