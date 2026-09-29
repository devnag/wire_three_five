import Proof.CaseAnalysis.WitnessFamilySparse

/-! The exact live entry ports of the existing family machine. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def port : Fin 104→Fin 3243:=Fin.addCases (m:=10) (n:=94) (motive:=fun _=>Fin 3243) headerSlot massSlot


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
