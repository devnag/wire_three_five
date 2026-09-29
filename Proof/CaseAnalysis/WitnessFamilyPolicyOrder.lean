import Proof.CaseAnalysis.WitnessFamilyCallDock
import Proof.CaseAnalysis.WitnessFamilyPolicyPorts
import Proof.CaseAnalysis.WitnessFamilyResourcesPolicy

/-! The exact fixed family port order combines the four retained external
words P/H/V/raw with the six legal-policy words and existing mass store. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def smallOrder : Fin 10→Fin 10:=![0,4,6,7,1,5,8,2,9,3]
def order : Fin 104→Fin (4+100):=
  Fin.addCases (m:=10) (n:=94) (motive:=fun _=>Fin (4+100))
    (fun i=>(smallOrder i).castAdd 94) (fun i=>i.natAdd 10)


def join {t : ℕ} (external : Fin 4→Fin t) (inside : Fin 100→Fin t) : Fin 104→Fin t:=
  (Fin.addCases (m:=4) (n:=100) (motive:=fun _=>Fin t) external inside) ∘ order

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
