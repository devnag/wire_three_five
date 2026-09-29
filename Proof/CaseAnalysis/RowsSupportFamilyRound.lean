import Proof.CaseAnalysis.RowsSupportSumRound
import Proof.CaseAnalysis.CloseoutWitnessFamilyLayout

/-! One complete original family field: the paid loader and verdict
prime feed the already-checked whole sum directly. Successful output
returns the same reusable bank and three ordered logical streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding CloseoutWitness
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def body {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  AppendBank.machine (e:=2) (SumRound.machine circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1704 s) (k : ℕ) (q : ℚ):=
  Composition.machine (TapeEmbedding.machine 1 FamilyLoad.prepare) (body circuit k q)

end
end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream.FamilyRound
