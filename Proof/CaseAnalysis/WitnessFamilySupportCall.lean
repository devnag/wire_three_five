import Proof.CaseAnalysis.WitnessSupportDock
import Proof.CaseAnalysis.WitnessFamilyCallDock

/-! Physical docking for the pinned3244-tape family supplier. This lemma
transports an actual supplier receipt; it does not assume that supplier exists. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportCall
open LocalBitMultitape FamilySparse
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots {t : ℕ} (fields : Fin 104→Fin t):=SupportDock.slots (FamilyCold.Call.slots fields)
def machine {t s : ℕ} (supplier : Machine 3244 s) (fields : Fin 104→Fin t):=RecoveryFocus.machine (slots fields) supplier


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySupportCall
