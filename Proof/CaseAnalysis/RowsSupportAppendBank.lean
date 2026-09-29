import Proof.CaseAnalysis.WitnessSupportDock
import Proof.Amplification.RecoveryFocusDock

/-! An actual extended worker runs below an unchanged ambient bank. The
added public tape stays last; old bank fields retain their original indices. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.AppendBank
open LocalBitMultitape CloseoutWitness.SupportDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine {t e s : ℕ} (p : Machine (t+1) s) : Machine (t+e+1) s:=
  RecoveryFocus.machine (slots (Fin.castAdd e)) p

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.AppendBank
