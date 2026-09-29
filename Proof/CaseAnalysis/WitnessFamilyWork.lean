import Proof.CaseAnalysis.WitnessFamilyDock

/-! The actual outer count enters its sentinel with one paid move and
then drives the unchanged complete family loop. Header workspace stays
outside the loop; its existing allocation is neither scanned nor copied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyWork
open LocalBitMultitape RecoveryRootRound
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def directions (i : Fin 3241) : HeadMove:=if i=3063 then .right else .stay
def move:=DecompositionCountPosition.move directions

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyWork
