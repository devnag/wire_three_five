import Proof.CaseAnalysis.WitnessSumBodyFields
import Proof.CaseAnalysis.WitnessSumHeader

/-! One raw sum header produces its actual native term-count record.
Rejected headers stop before the record append; the ordered term stream
and actual repeat driver come from the same canonical traversal. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumPrefix
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def first := TapeEmbedding.machine 18 SumGuard.machine
def machine := RecoveryGatedSequence.machine first SumCountStream.machine 499

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumPrefix
