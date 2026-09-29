import Proof.CaseAnalysis.WitnessFamilyPolicyOrder
import Proof.CaseAnalysis.WitnessFamilyCapacityJoin

/-! The actual paid P/H outputs and existing legal-policy ports feed one
whole-family call. The raw family and actual V remain separate old tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable {t : ℕ}
def external (E : ℕ) (source count raw : Fin t) : Fin 4→Fin (t+FamilyCapacity.Call.extra E):=
  ![FamilyCapacity.Call.slots E source (FamilyCapacity.pSlot E),
    FamilyCapacity.Call.slots E source (FamilyCapacity.hSlot E),
    FamilyCapacity.Call.old E count,FamilyCapacity.Call.old E raw]
def inside (e E : ℕ) (policy : Fin (LegalTemplate.tapes e)→Fin t) (i : Fin 100):=
  FamilyCapacity.Call.old E (policy (FamilyPolicyPorts.port e i))
def fields (e E : ℕ) (source count raw : Fin t) (policy : Fin (LegalTemplate.tapes e)→Fin t):=
  FamilyPolicyPorts.join (external E source count raw) (inside e E policy)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyFromPolicy
