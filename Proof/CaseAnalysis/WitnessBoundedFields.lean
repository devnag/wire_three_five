import Proof.CaseAnalysis.WitnessInput

/-! The existing bounded tagged header supplies the three cold inputs
and the actual mode bit. Payload lengths inherit its single N/16 guard. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def oracle (bits : List Bool):=RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 3)
def family (bits : List Bool):=RecoveryFixedUnpair.leftWord (CompetitorWitnessTriple.word bits 5)
def symmetric (bits : List Bool):=decide (CompetitorWitnessTriple.field bits 1=0)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.BoundedFields
