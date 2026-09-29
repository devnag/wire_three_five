import Proof.CaseAnalysis.RowsModeHashRow

/-! The original prefix depth drives all required Toeplitz rows in order.
The rank-zero/depth-zero case exhausts the actual driver without a row call. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashLoop
open LocalBitMultitape RecoveryRootRound RepairSource.VerifierDecoding ExtDecompositionBatch CloseoutRowsModeHashReturned CloseoutRowsModeHashRow
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=CloseoutRowsDegreeLoop.machine CloseoutRowsModeHashRow.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashLoop
