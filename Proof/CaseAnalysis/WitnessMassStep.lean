import Proof.CaseAnalysis.WitnessMassPrepare

/-! One complete direct absolute-mass update: clear, widen the retained
coefficient fields, add, and copy the exact accumulator back. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassStep
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def lastProgram:=RecoveryFocus.machine MassPrepare.old bodyTail
def machine:=Composition.machine MassPrepare.machine lastProgram

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassStep
