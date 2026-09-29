import Proof.CaseAnalysis.CloseoutWitnessFamilyColdRun

/-! Only the ten paid metadata words and existing mass store are live at
the cold family entry. Every private coordinate is genuinely blank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def headerSlot (i : Fin 10) : Fin 3243:=![720,2501,2525,2526,2530,3034,3035,3238,3241,3242] i
def massSlot (i : Fin 94) : Fin 3243:=⟨725+i.val,by omega⟩

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilySparse
