import Proof.CaseAnalysis.WitnessFamilySupportCall
import Proof.CaseAnalysis.WitnessFamilyFromPolicyLayout

/-! The original paid capacity prefix carries the added support stream
unchanged into the actual family dock. No copy or extra reset is executed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
namespace FamilySupportPrefix

def machine {t s : ℕ} (p : Machine t s):=TapeEmbedding.machine 1 (TapeEmbedding.machine 3243 p)


end FamilySupportPrefix

namespace FamilySupportFromPolicy
open LocalBitMultitape
variable {t s : ℕ}
def first (E K : ℕ) (source : Fin t):=FamilySupportPrefix.machine (FamilyCapacity.Call.machine E K source)
def second (supplier : Machine 3244 s) (e E : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t):=
  FamilySupportCall.machine supplier (FamilyFromPolicy.fields e E source count raw policy)
def machine (supplier : Machine 3244 s) (e E K : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t):=
  Composition.machine (first E K source) (second supplier e E source count raw policy)

end FamilySupportFromPolicy
end
end NearCubicWires.RepairOrdinary.CloseoutWitness
