import Proof.CaseAnalysis.WitnessOracleCapCall

/-! The same actual PCPP output supplies systematic, auxiliary and clause
counts. One paid tag skip precedes the existing three-natural-field reader;
the source and all three templates return at head zero for later consumers. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SourceFields
open LocalBitMultitape RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def skipSlots : Fin 3→Fin 33:=![0,31,32]
def nodeSlots (i : Fin 31) : Fin 33:=i.castAdd 2
noncomputable def skip:=RecoveryFocus.machine skipSlots (PCPPQueryField.machine false)
noncomputable def read:=RecoveryFocus.machine nodeSlots PCPPNativeNodeRead.machine
noncomputable def raw:=Composition.machine skip read
def rawBudget (a b c : ℕ):=PCPPQueryField.fieldCost 3+1+PCPPNativeNodeRead.budget a b c
noncomputable def machine:=Rewind.machine raw
def budget (a b c : ℕ):=2*rawBudget a b c+2

end NearCubicWires.RepairOrdinary.CloseoutWitness.SourceFields
