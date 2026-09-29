import Proof.Hierarchy.CompetitorWitnessCap

/-! The cap and canonical-header consumers share their actual input/witness
tapes. The two cap outputs sit outside all 148 header tapes. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 150 := ![0,1,148,149]
noncomputable def cap := RecoveryFocus.machine slots CompetitorWitnessCap.guard
noncomputable def header := TapeEmbedding.machine 2 CompetitorWitnessHeader.machine

end NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
