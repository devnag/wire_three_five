import Proof.CaseAnalysis.RowsCircuitBottomReturned
import Proof.CaseAnalysis.WitnessSumCursor

/-! Enter the actual term driver with one physical move, then run the
whole sum body. The head identities also provide the successful return
boundary without traversing any retained output prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumWork
