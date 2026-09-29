import Proof.CaseAnalysis.WitnessFamilyReload

/-! Whole-family preparation: the two paid erase sweeps, both retained
field copies and the initial false verdict are one actual execution.
The incoming source policy, zero mass store and stream cursors survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPrepare
open LocalBitMultitape RecoveryRootRound
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def bank:=TapeEmbedding.machine 2 FamilyBank.machine
def machine:=Composition.machine bank FamilyReload.machine

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPrepare
